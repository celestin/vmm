/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

module cntrlr(clk, reset, busAddr, busData, busRdWr_N, adxStrb, rdWr_N, ce0_N,
	ce1_N, ce2_N, ce3_N, ramAddr, ramData);

parameter RAM_ADDR_WDTH = 9;
parameter NUM_OF_SRAMS = 4;
input clk, reset, busRdWr_N, adxStrb; 
input [31:0] busAddr;
inout [7:0] busData;
output rdWr_N, ce0_N, ce1_N, ce2_N, ce3_N;
output [RAM_ADDR_WDTH-1:0] ramAddr;
inout [7:0] ramData;


reg [1:0] state, nxState;
wire nxvalid;
reg valid;
reg[3:0] nxCe_, ce_;
reg nxRdWr_, rdWr_N;
reg outEn;
reg [7:0] dataWr, dataRd;
reg [31:0] address;
reg busOe, readWrite_;

parameter IDLE = 0, START = 1, WRITE0 = 2, WRITE1 = 3;

/** IO PADS for bidirectionals ***/
wire[1:0] bruce = state;
wire [1:0] addr_part;

assign  ramData = (outEn) ? dataWr : 8'bzzzzzzzz;
assign busData = (busOe) ? dataRd : 8'bzzzzzzzz;

assign ce0_N = ce_[0];
assign ce1_N = ce_[1];
assign ce2_N = ce_[2];
assign ce3_N = ce_[3];

assign ramAddr = address[RAM_ADDR_WDTH-1:0];
assign addr_part = address[RAM_ADDR_WDTH+1: RAM_ADDR_WDTH];

always @(state or ce_ or readWrite_ or valid)
begin 

   nxState = state;
   nxCe_ = ce_;
   nxRdWr_ = 1'b1;
   outEn = 1'b0;

   case(state)
      IDLE: begin
         if(valid)
            nxState = START;
 	 if(valid & readWrite_) begin
        if (NUM_OF_SRAMS == 1) begin
            nxCe_ = 4'b1110;
        end
        else if (NUM_OF_SRAMS == 2) begin
            if (address[RAM_ADDR_WDTH] == 1'b0)
               nxCe_ = 4'b1110;
            else
               nxCe_ = 4'b1101;
        end
        else begin //4 devices
	        case(addr_part)
	           2'b00: nxCe_= 4'b1110;
	           2'b01: nxCe_= 4'b1101;
	           2'b10: nxCe_= 4'b1011;
	           2'b11: nxCe_= 4'b0111;
	        endcase
        end
	 end
	 else nxCe_ = 4'b1111;
      end

      START: begin
         if(readWrite_) begin // read operation
  	    nxState = IDLE;
	    nxCe_ = 4'b1111;
         end
	 else begin  // write operation
  	    nxRdWr_ = 1'b0;         
        if (NUM_OF_SRAMS == 1) begin
            nxCe_ = 4'b1110;
        end
        else if (NUM_OF_SRAMS == 2) begin
            if (address[RAM_ADDR_WDTH] == 1'b0)
               nxCe_ = 4'b1110;
            else
               nxCe_ = 4'b1101;
        end
        else begin //4 devices
	        case(addr_part)
	           2'b00: nxCe_= 4'b1110;
	           2'b01: nxCe_= 4'b1101;
	           2'b10: nxCe_= 4'b1011;
	           2'b11: nxCe_= 4'b0111;
	        endcase
        end
            outEn = 1'b1;
  	    nxState = WRITE0;
	 end
      end

      WRITE0: begin
	 nxRdWr_ = 1'b1;         
	 outEn = 1'b1;
	 nxCe_ = 4'b1111;
	 nxState = WRITE1;
      end
 
      WRITE1: begin
	 outEn = 1'b1;
         nxState = IDLE;
      end

   endcase
end

assign nxvalid = adxStrb & (state == IDLE); // diregard other stuff while busy 

always @(posedge clk)
begin
   if(reset) begin
      state = IDLE;
      ce_ <= #1 4'b1111;
   end
   else begin
      state <= #1 nxState;
   end

   address <= #1 (nxvalid) ? busAddr : address;
   dataWr <= #1 (nxvalid & ~busRdWr_N) ? busData : dataWr;
   readWrite_ <= #1 (nxvalid) ? busRdWr_N : readWrite_;
   ce_ <= #1 nxCe_;
   rdWr_N <= #1 nxRdWr_; 
   dataRd <= #1 (rdWr_N & ~&ce_) ? ramData : dataRd;
   busOe <= #1 (rdWr_N & ~&ce_);
   valid <= #1 nxvalid;
end

initial
begin
  /* 
  $monitor($time,,"%b %b %b %b %b %b %b %b %b", reset, state, adxStrb, 
	ce_, rdWr_N, ramAddr, ramData, busAddr, busData);
  */
end
endmodule
