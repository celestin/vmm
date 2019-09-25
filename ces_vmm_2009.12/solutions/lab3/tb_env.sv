`ifndef TB_ENV__SV
`define TB_ENV__SV

`include "test_cfg.sv"
`include "Packet.sv"

// Lab 3 - Add include statement for Packet_atomic_gen.sv and GenCovCallbacks.sv
// ToDo
//`include "Packet_atomic_gen.sv"
`include "GenCovCallbacks.sv"


// Second part of Lab 3 (scoreboard)
// Lab 3 - Add include statement for scoreboard.sv and GenSbCallbacks.sv
// ToDo
`include "scoreboard.sv"
`include "GenSbCallbacks.sv"


class tb_env extends vmm_env;
   test_cfg cfg;
   Packet blueprint;
   Packet_atomic_gen gen;

   // Lab 3 - Create an instance of GenCovCallbacks
   // ToDo
   GenCovCallbacks gen_cov_cb;


   // Second part of Lab 3 (scoreboard)
   // Lab 3 - Create an instance of scoreboard and GenSbCallbacks
   // ToDo
   scoreboard sb;
   GenSbCallbacks gen_sb_cb;


   `vmm_env_member_begin(tb_env)
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
   this.gen = new("gen", 0);
   this.gen.stop_after_n_insts = this.cfg.run_for_n_packets;
   this.blueprint = new();
   this.blueprint.valid_sa = this.cfg.iports_in_use.find_index() with (item == 1);
   this.blueprint.valid_da = this.cfg.oports_in_use.find_index() with (item == 1);
   this.gen.randomized_obj = this.blueprint;
   this.gen.out_chan.sink();

   // Lab 3 - Construct and register the functional coverage callback object
   // ToDo
   this.gen_cov_cb = new();
   this.gen.append_callback(gen_cov_cb);


   // Second part of Lab 3 (scoreboard)
   // Lab 3 - Construct the scoreboard object
   // ToDo
   this.sb = new(this.cfg);

   // Lab 3 - Construct and register the scoreboard callback object
   // ToDo
   this.gen_sb_cb = new(this.sb);
   this.gen.append_callback(gen_sb_cb);


endfunction: build

task tb_env::reset_dut();
   super.reset_dut();
endtask: reset_dut
   
task tb_env::cfg_dut();
   super.cfg_dut();
endtask: cfg_dut

task tb_env::wait_for_end();
   super.wait_for_end();
   this.gen.notify.wait_for(Packet_atomic_gen::DONE);
endtask: wait_for_end

task tb_env::cleanup();
   super.cleanup();
endtask: cleanup

task tb_env::report() ;
   super.report();
   `vmm_note(log, this.cfg.psdisplay());

   // Second part of Lab 3 (scoreboard)
   // Lab 3 - call scoreboard's report() method
   // ToDo
   this.sb.report();

endtask: report

`endif // TB_ENV__SV
