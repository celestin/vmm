import vmm::*;
import intel::*;

module top;

host_if       cpu_bus;   // From DUT

logic [31:0] cs;
logic        rst;
logic        clk;

assign cpu_bus.sel = cs[0];
dut dut(cpu_bus, rst, clk);


intel_if intel_bus;

assign cpu_bus.addr    = intel_bus.addr;
assign cpu_bus.sel     = intel_bus.cs;
alias cpu_bus.data, intel_bus.data;
assign cpu_bus.rd      = intel_bus.read;
assign cpu_bus.wr      = intel_bus.write;
assign intel_bus.ready = cpu_bus.rdy;

program;

class test_cfg;
   rand bit use_intel_cpu;

   rand int unsigner run_for;

   constraint always_use_intel {
      use_intel_cpu == 1;
   }

   constraint reasonable {
	run_for < 1000;
   }
endclass: test_cfg

class dut_env extends vmm_env;

   test_cfg                     cfg;
   intel_master                 cpu;
   intel_transaction_atomic_gen gen;

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
      if (this.cfg.use_intel_cpu) begin
         this.cpu = new("Host", intel_bus.master);
         this.gen = new("Generator", 0, this.cpu.in_chan);

         // CPU BFM needed right away to configure DUT
         this.cpu.start_xactor();
      end
   endfunction: build

   virtual function void start();
      super.start();
      this.gen.start_xactor();
   endfunction: start

   virtual task          wait_for_end();
      super.wait_for_end();
      repeat (this.cfg.run_for) begin
         this.cpu.notify.wait_for(this.cpu.TRANSACTION_COMPLETED);
      end
   endtask: wait_for_end

endclass: dut_env

const dut_env env = new;

endprogram

endmodule: top
