//
// (c) Copyright 2000, Qualis Design Corporation
// All Rights Reserved
//
//    This source file may be used and distributed without restriction
//    provided that this copyright statement is not removed from the file
//    and that any derivative work contains this copyright notice.
//
// Description
//    Functional model of the SQUAT device
//
// Author:      $Author: janick $
// Revision:    $Revision: 1.2 $
//
// Changes:	1. implemented a round robin priority scheme for inputs

module squat(
	     //
	     // 4 x Level 1 Utopia ATM layer Rx Interfaces
	     //
             Rx_clk_0,  Rx_clk_1,  Rx_clk_2,  Rx_clk_3,
             Rx_data_0, Rx_data_1, Rx_data_2, Rx_data_3,
             Rx_soc_0,  Rx_soc_1,  Rx_soc_2,  Rx_soc_3, 
             Rx_en_0,   Rx_en_1,   Rx_en_2,   Rx_en_3,  
             Rx_clav_0, Rx_clav_1, Rx_clav_2, Rx_clav_3,
             
	     //
	     // 4 x Level 1 Utopia ATM layer Tx Interfaces
	     //
             Tx_clk_0,   Tx_clk_1,   Tx_clk_2,   Tx_clk_3,
             Tx_data_0,  Tx_data_1,  Tx_data_2,  Tx_data_3,
             Tx_soc_0,   Tx_soc_1,   Tx_soc_2,   Tx_soc_3, 
             Tx_en_0,    Tx_en_1,    Tx_en_2,    Tx_en_3,  
             Tx_clav_0,  Tx_clav_1,  Tx_clav_2,  Tx_clav_3,
             
	     //
	     // Utopia Level 2 parallel management interface
	     //
	     BusMode, Addr, Sel, Data, Rd_DS, Wr_RW, Rdy_Dtack,
             
	     //
	     // Miscellaneous control interfaces
	     //
	     rst, clk);

//
// 4 x Level 1 Utopia Rx Interfaces
//
   output       Rx_clk_0,  Rx_clk_1,  Rx_clk_2,  Rx_clk_3;
   input [7:0]  Rx_data_0, Rx_data_1, Rx_data_2, Rx_data_3;
   input        Rx_soc_0,  Rx_soc_1,  Rx_soc_2,  Rx_soc_3; 
   output       Rx_en_0,   Rx_en_1,   Rx_en_2,   Rx_en_3;  
   input        Rx_clav_0, Rx_clav_1, Rx_clav_2, Rx_clav_3;

//
// 4 x Level 1 Utopia Tx Interfaces
//
   output       Tx_clk_0,   Tx_clk_1,   Tx_clk_2,   Tx_clk_3;
   output [7:0] Tx_data_0,  Tx_data_1,  Tx_data_2,  Tx_data_3;
   output       Tx_soc_0,   Tx_soc_1,   Tx_soc_2,   Tx_soc_3; 
   output       Tx_en_0,    Tx_en_1,    Tx_en_2,    Tx_en_3;  
   input        Tx_clav_0,  Tx_clav_1,  Tx_clav_2,  Tx_clav_3;

//
// Intel-style Utopia parallel management interface
//
   input        BusMode;
   input [11:0] Addr;
   input        Sel;
   inout [ 7:0] Data;
   input        Rd_DS;
   input        Wr_RW;
   output       Rdy_Dtack;
   
//
// Miscellaneous control interfaces
//
   input        rst;
   input        clk;


//
// Register file
//
   reg [15:0]   regfile ['h00:'hff];

//
// Hardware reset
//
   reg          reset;
always
begin: detect_reset
   reset = 1'b0;
   while (rst !== 1'b1) @ (posedge clk);
   reset = 1'b1;
   while (rst === 1'b1) @ (posedge clk);
end

always
begin: do_reset
   integer i;

   wait (reset);
   // Reset the register file
   for (i = 'h00; i <= 'hff; i = i + 1) begin
      regfile[i] = 16'h0000;
   end
   // Disable all blocks
   disable mgmt_if;
   disable main;

   atm_rx_0.reset(1);
   atm_rx_1.reset(1);
   atm_rx_2.reset(1);
   atm_rx_3.reset(1);

   atm_tx_0.reset(1);
   atm_tx_1.reset(1);
   atm_tx_2.reset(1);
   atm_tx_3.reset(1);
   
   wait (!reset);

   atm_rx_0.reset(0);
   atm_rx_1.reset(0);
   atm_rx_2.reset(0);
   atm_rx_3.reset(0);

   atm_tx_0.reset(0);
   atm_tx_1.reset(0);
   atm_tx_2.reset(0);
   atm_tx_3.reset(0);
end


//
// Management interface
//

   // AC timing characteristics
   parameter t4 = 10;
   parameter t6 = 15;
   parameter t7 = 10;
   parameter t9 = 15;

   // Output drivers
   reg [7:0] Data_out;
   assign    Data = Data_out;
   reg       Rdy_Dtack;

// Task to perform actual register write
task reg_write;
   input [8:0] addr;
   input [7:0] data;

   reg [15:0] config;
begin
   // We use big endian
   config = regfile[addr[8:1]];
   if (addr[0] == 1'b0) config[ 7:0] = data;
   else                 config[15:8] = data;
   regfile[addr[8:1]] = config;
end
endtask

// Function to perform actual register read
function [7:0] reg_read;
   input [8:0] addr;

   reg [15:0] config;
begin
   // We use big endian
   config = regfile[addr[8:1]];
   if (addr[0] == 1'b0) reg_read = config[ 7:0];
   else                 reg_read = config[15:8];
end
endfunction

always
begin: mgmt_if
   Data_out  = 8'hzz;
   Rdy_Dtack = 1'bz;
   
   // Wait for reset to go away
   wait (!reset);

   // Normal operation
   forever begin: do_cycle
      integer delay;

      @ (negedge Rd_DS or negedge Wr_RW);
      // Are we selected
      if (Sel !== 1'b0) disable do_cycle;
      // or in the correct mode?
      if (!(BusMode === 1'b1 && Wr_RW == 1'b0 || Rd_DS === 1'b0))
         disable do_cycle;
      
      // Assert Rdy/Dtack right away
      #(t6);
      Rdy_Dtack <= 1'b0;
      
      // Which one was it?
      if (BusMode === 1'b0) begin
         // 68k mode cycle
         if (Wr_RW === 1'b0) begin
            // Write cycle
            @ (posedge Rd_DS);
            reg_write(Addr, Data);
         end
         else begin
            // Read cycle
            Data_out <= #(t4) reg_read(Addr);
            @ (posedge Rd_DS);
            Data_out <= #(t9) 8'hZZ;
         end
      end
      else if (Rd_DS === 1'b0) begin
         // Intel mode read cycle
         Data_out <= #(t4) reg_read(Addr);
         @ (posedge Rd_DS);
         Data_out <= #(t9) 8'hZZ;
      end
      else begin
         // Intel mode write cycle
         @ (posedge Wr_RW);
         reg_write(Addr, Data);
      end

      // Terminate the cycle
      Rdy_Dtack <= #(t7) 1'bz;
   end
end


//
// ATM-layer Utopia interface receivers
//
   
utopia1_atm_rx atm_rx_0(.clk  (Rx_clk_0),
                        .data (Rx_data_0),
                        .soc  (Rx_soc_0),
                        .en   (Rx_en_0),
                        .clav (Rx_clav_0));

utopia1_atm_rx atm_rx_1(.clk  (Rx_clk_1),
                        .data (Rx_data_1),
                        .soc  (Rx_soc_1),
                        .en   (Rx_en_1),
                        .clav (Rx_clav_1));

utopia1_atm_rx atm_rx_2(.clk  (Rx_clk_2),
                        .data (Rx_data_2),
                        .soc  (Rx_soc_2),
                        .en   (Rx_en_2),
                        .clav (Rx_clav_2));

utopia1_atm_rx atm_rx_3(.clk  (Rx_clk_3),
                        .data (Rx_data_3),
                        .soc  (Rx_soc_3),
                        .en   (Rx_en_3),
                        .clav (Rx_clav_3));

                       
//
// ATM-layer Utopia interface transmitters
//


utopia1_atm_tx atm_tx_0(.clk  (Tx_clk_0),
                        .data (Tx_data_0),
                        .soc  (Tx_soc_0),
                        .en   (Tx_en_0),
                        .clav (Tx_clav_0));

utopia1_atm_tx atm_tx_1(.clk  (Tx_clk_1),
                        .data (Tx_data_1),
                        .soc  (Tx_soc_1),
                        .en   (Tx_en_1),
                        .clav (Tx_clav_1));

utopia1_atm_tx atm_tx_2(.clk  (Tx_clk_2),
                        .data (Tx_data_2),
                        .soc  (Tx_soc_2),
                        .en   (Tx_en_2),
                        .clav (Tx_clav_2));

utopia1_atm_tx atm_tx_3(.clk  (Tx_clk_3),
                        .data (Tx_data_3),
                        .soc  (Tx_soc_3),
                        .en   (Tx_en_3),
                        .clav (Tx_clav_3));

//
// Generate the CRC-8 syndrom table
//
reg [7:0] syndrom[0:255];
initial
begin: gen_syndrom
   integer i;
   reg [7:0] sndrm;
   
   for (i = 0; i < 256; i = i + 1 ) begin
      sndrm = i;
      repeat (8) begin
         if (sndrm[7] === 1'b1)
            sndrm = (sndrm << 1) ^ 8'h07;
         else
            sndrm = sndrm << 1;
      end
      syndrom[i] = sndrm;
   end
end

//
// Function to compute the HEC value
//
function [7:0] hec;
   input [31:0] hdr;

   integer i;
begin
   hec = 8'h00;
   repeat (4) begin
      hec = syndrom[hec ^ hdr[31:24]];
      hdr = hdr << 8;
   end
   hec = hec ^ 8'h55;
end
endfunction


//
// Rewriting and forwarding process
//

always
begin: main
   reg [53*8:1] cell;
   reg [3:0] RoundRobin;
   reg [3:0] Request;

   // Useful fields
   `define HEC     49*8  :49*8-7
   `define HEADER  53*8  :50*8-7
   `define UNI_VPI 53*8-4:52*8-3
   `define NNI_VPI 53*8  :52*8-3

   // Wait for the reset to go away
   wait (!reset);
   RoundRobin = 4'b0001;
   $write("Main go!\n");

   forever begin: next_cell
      reg [ 7:0] uni_vpi;
      reg [ 3:0] forward;
      reg [11:0] nni_vpi;

      // Poll the Rx interfaces
      wait (atm_rx_0.cell_bfr[0] !== 1'bx ||
            atm_rx_1.cell_bfr[0] !== 1'bx ||
            atm_rx_2.cell_bfr[0] !== 1'bx ||
            atm_rx_3.cell_bfr[0] !== 1'bx);

      // Which one has something for us??
      // Round Robin Priority
      Request = {
        atm_rx_3.cell_bfr[0]!==1'bx ? 1'b1 : 1'b0,
        atm_rx_2.cell_bfr[0]!==1'bx ? 1'b1 : 1'b0,
        atm_rx_1.cell_bfr[0]!==1'bx ? 1'b1 : 1'b0,
        atm_rx_0.cell_bfr[0]!==1'bx ? 1'b1 : 1'b0
        };
      Request = RoundRobin & Request;
      case (Request)
        4'b0001 : begin
            cell = atm_rx_0.cell_bfr;
            atm_rx_0.cell_bfr[0] = 1'bx;
          end
        4'b0010 : begin
            cell = atm_rx_1.cell_bfr;
            atm_rx_1.cell_bfr[0] = 1'bx;
          end
        4'b0100 : begin
            cell = atm_rx_2.cell_bfr;
            atm_rx_2.cell_bfr[0] = 1'bx;
          end
        4'b1000 : begin
            cell = atm_rx_3.cell_bfr;
            atm_rx_3.cell_bfr[0] = 1'bx;
          end
      endcase
      RoundRobin = {RoundRobin[2:0], RoundRobin[3]};

      if (Request) begin
        $write("Processing cell\n");
        // Ignore this cell if it is corrupted
        if (cell[`HEC] !== hec(cell[`HEADER])) begin
          $write("cell is corrupted\n");
          disable next_cell;
        end

        $write("Rewriting cell\n");
        uni_vpi = cell[`UNI_VPI];

        // Lookup the configuration for this VPI value
        {forward, nni_vpi} = regfile[uni_vpi];

        // Rewrite the cell
        cell[`NNI_VPI] = nni_vpi;

        // Recompute the HEC
        cell[`HEC] = hec(cell[`HEADER]);

        $write("forwarding cell %b\n", forward);
        // Forward the cell to all output interfaces
        // that can accept it. Otherwise, wait for the
        // output buffers to be available
        while (forward != 4'b0000) begin
           wait ((forward[0] && atm_tx_0.cell_bfr[0] === 1'bx) ||
                 (forward[1] && atm_tx_1.cell_bfr[0] === 1'bx) ||
                 (forward[2] && atm_tx_2.cell_bfr[0] === 1'bx) ||
                 (forward[3] && atm_tx_3.cell_bfr[0] === 1'bx));
           
           if (forward[0] && atm_tx_0.cell_bfr[0] === 1'bx) begin
              $write("Forward to port 0\n");
              atm_tx_0.cell_bfr = cell;
              forward[0] = 1'b0;
           end
           if (forward[1] && atm_tx_1.cell_bfr[0] === 1'bx) begin
              $write("Forward to port 1\n");
              atm_tx_1.cell_bfr = cell;
              forward[1] = 1'b0;
           end
           if (forward[2] && atm_tx_2.cell_bfr[0] === 1'bx) begin
              $write("Forward to port 2\n");
              atm_tx_2.cell_bfr = cell;
              forward[2] = 1'b0;
           end
           if (forward[3] && atm_tx_3.cell_bfr[0] === 1'bx) begin
              $write("Forward to port 3\n");
              atm_tx_3.cell_bfr = cell;
              forward[3] = 1'b0;
           end
        end
     end
   end
end

endmodule
