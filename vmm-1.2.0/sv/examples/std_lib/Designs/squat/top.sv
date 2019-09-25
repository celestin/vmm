import vmm::*;
import intel::*;
import atm::*;


module top;

//
// 4 x Level 1 Utopia Interfaces
//
utopia1_if [3:0] uif;

//
// Intel-style Utopia parallel management interface
//
reg      BusMode;
intel_if cpu_bus;
   
//
// Miscellaneous control interfaces
//
reg       rst;
reg       clk;

squat dut(
	     //
	     // 4 x Level 1 Utopia ATM layer Rx Interfaces
	     //
             uif[0].rx_clk,  uif[1].rx_clk,  uif[2].rx_clk,  uif[3].rx_clk,
             uif[0].rx_data, uif[1].rx_data, uif[2].rx_data, uif[3].rx_data,
             uif[0].rx_soc,  uif[1].rx_soc,  uif[2].rx_soc,  uif[3].rx_soc, 
             uif[0].rx_en,   uif[1].rx_en,   uif[2].rx_en,   uif[3].rx_en,  
             uif[0].rx_clav, uif[1].rx_clav, uif[2].rx_clav, uif[3].rx_clav,
             
	     //
	     // 4 x Level 1 Utopia ATM layer Tx Interfaces
	     //
             uif[0].tx_clk,   uif[1].tx_clk,   uif[2].tx_clk,   uif[3].tx_clk,
             uif[0].tx_data,  uif[1].tx_data,  uif[2].tx_data,  uif[3].tx_data,
             uif[0].tx_soc,   uif[1].tx_soc,   uif[2].tx_soc,   uif[3].tx_soc, 
             uif[0].tx_en,    uif[1].tx_en,    uif[2].tx_en,    uif[3].tx_en,  
             uif[0].tx_clav,  uif[1].tx_clav,  uif[2].tx_clav,  uif[3].tx_clav,
             
	     //
	     // Utopia Level 2 parallel management interface
	     //
	     BusMode,
             cpu_if.addr, cpu_if.cs, cpu_if.data,
             cpu_if.read, cpu_if.write, cpu_if.ready,
             
	     //
	     // Miscellaneous control interfaces
	     //
	     rst, clk);


//
// System Clock
//
always
begin
   #5 clk = 1;
   #5 clk = 0;
end

program;

class vpi_cfg;
   rand bit [ 3:0] forward = 4'h0;
   rand bit [11:0] nni_vpi = 12'h000;
endclass

class dut_cfg;
   rand vpi_cfg uni_vpi[256];

   function new();
      foreach (uni_vpi[i]) begin
         uni_vpi[i] = new;
      end
   endfunction
endclass

class test_cfg;
   rand bit         use_intel_cpu;
   rand utopia1_cfg utopia1_ports;
   rand dut_cfg     dut;

   rand int unsigner run_for;

   constraint always_use_intel {
      use_intel_cpu == 1;
   }

   constraint octet_flow_control {
      utopia1_ports.handshake == utopia1_cfg::OCTET;
   }

   constraint no_udf_channel {
      utopia1_ports.use_udf_channel == 0;
   }

   constraint reasonable {
	run_for < 1000;
   }

   function new();
      this.utopia1_ports = new;
      this.dut           = new;
   endfunction: new

endclass: test_cfg


class sb_utopia1_atm_callbacks extends utopia1_atm_callbacks;
   virtual task post_cell_tx(utopia1_atm_layer xactor,
                             const atm_cell    cell
                             const utopia1_udf udf)
      squat_self_check.injected_cell(cell, xactor.stream_id);
   endtask
endclass: sb_utopia1_atm_callbacks


class dut_env extends vmm_env;

   test_cfg            cfg;
   intel_master        intel_cpu;
   utopia1_atm_layer   atm[4];
   atm_cell_atomic_gen gen[4];


   function new()
      super.new();
      this.cfg = new;
   endfunction: new


   virtual function void gen_cfg()
      super.gen_cfg();
      if (!this.cfg.randomize()) begin
         vmm_fatal(log, "Failed to randomize test configuration");
      end
   endfunction: gen_cfg


   virtual function void build()
      super.build();

      squat_self_check.configure(this.cfg);

      if (this.cfg.use_intel_cpu) begin
         this.intel_cpu = new("Host", cpu_bus.master);

         // CPU BFM needed right away to configure DUT
         this.intel_cpu.start_xactor();
      end

      for (int i = 0; i < 4; i++) begin
         atm_nni_cell nni = new;
         atm[i] = new(psprintf("Port #%0d", i), i, this.cfg.utopia1_ports,
                   nni, uif[i].atm_layer);
         begin
            sb_utopia1_atm_callbacks cb = new;
            atm[i].append_callback(cb);
         end

         gen[i] = new(psprintf("Source #%0d, i), i, atm[i].cell_in_chan);
      end
   endfunction: build


   virtual task reset_dut();
      super.reset_dut();

      top.rst = 1;
      repeat (2) @ (posedge top.clk);
      top.rst <= 0;
   endtask


   virtual task cfg_dut();
      super.cfg_dut();

      foreach (this.cfg.dut.uni_vpi[i]) begin
         bit [7:0] vpi;
         bit [15:0] data;

         vpi = i;
         data = {this.cfg.dut.uni_vpi[i].forward,
                 this.cfg.dut.uni_vpi[i].nni_vpi};

	 if (this.cfg.use_intel_cpu) begin
            bit ok;
            intel_cpu.write({i, 1'b0}, 0, data[7:0], ok);
            if (!ok) begin
               `vmm_error(log, psprintf("Error while writing 'h%h to 'h%h@%b",
                                        data[7:0], {addr, 1'b0}, 0));
            end 
            intel_cpu.write({i, 1'b1}, 0, data[15:8], ok);
            if (!ok) begin
               `vmm_error(log, psprintf("Error while writing 'h%h to 'h%h@%b",
                                        data[15:8], {addr, 1'b1}, 0));
            end 
         end
      end
   endtask


   virtual function void start();
      super.start();
      foreach (atm[i]) begin
         this.atm[i].start_xactor();
         this.gen[i].start_xactor();

         // Sink received cells and forward to scoreboard to be checked
         fork
            automatic int j = i;
            automatic atm_cell cell;
            forever begin
               atm[j].cell_out_chan.get(cell);
               squat_self_check.received_cell(cell, j);
               this.cfg.run_for--;
            end
         join none
      end
   endfunction: start


   virtual task wait_for_end();
      super.wait_for_end();
      wait (this.cfg.run_for <= 0);
   endtask: wait_for_end


   virtual function void stop();
      super.stop();
      foreach (atm[i]) begin
         this.gen[i].stop_xactor();
      end

      // Wait for the DUT to drain...
      // ... i.e. 500 clock cycles without any activity
      //     on the output interfaces
      for (int n = 500; n >= 0; n--) begin
         @ (posedge clk);
         foreach (uif[i]) begin
            if (uif[i].tx_en == 1'b1 ||
                uif[i].rx_en == 1'b1) begin
               n = 500;
               break;
            end
         end
      end
      
   endfunction: start

endclass: dut_env

const dut_env env = new;

endprogram
endmodule
