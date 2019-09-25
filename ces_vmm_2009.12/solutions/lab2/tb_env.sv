`ifndef TB_ENV__SV
`define TB_ENV__SV

`include "test_cfg.sv"
// Lab 2 - Add include statement for Packet.sv
// ToDo
`include "Packet.sv"


class tb_env extends vmm_env;
   test_cfg cfg;
   // Lab 2 - Create an instance of Packet call it blueprint
   // ToDo
   Packet blueprint;

   // Lab 2 - Create an instance of Packet_atomic_gen
   // ToDo
   Packet_atomic_gen gen;

   `vmm_env_member_begin(tb_env)
      // Lab 2 - Add the Packet_atomic_gen object as a xactor member
      // ToDo
      `vmm_env_member_xactor(gen, DO_ALL)
   `vmm_env_member_end(tb_env)
    
   extern function new();
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   extern virtual task wait_for_end();
   extern virtual task cleanup();
   extern virtual task report();
endclass: tb_env

function tb_env::new();
   super.new();
   cfg = new();
endfunction: new

function void tb_env::gen_cfg();
   super.gen_cfg();
   if (!cfg.randomize())
      `vmm_fatal(log, "Test Configuration Failed Randomization");
   `vmm_note(log, cfg.psdisplay());
endfunction: gen_cfg

function void tb_env::build();
   super.build();
   // Lab 2 - Construct and configure the Packet_atomic_gen object
   // ToDo
   this.gen = new("gen", 0);
   this.gen.stop_after_n_insts = this.cfg.run_for_n_packets;
   this.blueprint = new();
   this.blueprint.valid_sa = this.cfg.iports_in_use.find_index() with (item == 1);
   this.blueprint.valid_da = this.cfg.oports_in_use.find_index() with (item == 1);
   this.gen.randomized_obj = this.blueprint;
   this.gen.out_chan.sink();
endfunction: build

task tb_env::reset_dut();
   super.reset_dut();
endtask: reset_dut
   
task tb_env::cfg_dut();
   super.cfg_dut();
endtask: cfg_dut

task tb_env::wait_for_end();
   super.wait_for_end();
   // Lab 2 - Wait for Packet_atomic_gen object's DONE flag to be set
   // ToDo
   this.gen.notify.wait_for(Packet_atomic_gen::DONE);
endtask: wait_for_end

task tb_env::cleanup();
   super.cleanup();
endtask: cleanup

task tb_env::report() ;
   super.report();
   // Lab 2 - Display test configuration
   // ToDo
   `vmm_note(log, this.cfg.psdisplay());
endtask: report

`endif // TB_ENV__SV
