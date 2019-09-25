`ifndef TB_ENV__SV
`define TB_ENV__SV

// Lab 1 - Add include statement for test_cfg.sv
// ToDo
`include "test_cfg.sv"


class tb_env extends vmm_env;
   // Lab 1 - Create an instance of test_cfg
   // ToDo
   test_cfg cfg;


   // `vmm_env_member macro will manage start() and stop() methods of the xactor for you
   `vmm_env_member_begin(tb_env)
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
   // Lab 1 - Construct test_cfg object
   // ToDo
   cfg = new();
endfunction: new

function void tb_env::gen_cfg();
   super.gen_cfg();
   // Lab 1 - Randomize test_cfg object
   // ToDo
   if (!cfg.randomize())
      `vmm_fatal(log, "Test Configuration Failed Randomization");
   `vmm_note(log, cfg.psdisplay());
endfunction: gen_cfg

function void tb_env::build();
   super.build();
endfunction: build

task tb_env::reset_dut();
   super.reset_dut();
endtask: reset_dut
   
task tb_env::cfg_dut();
   super.cfg_dut();
endtask: cfg_dut

task tb_env::wait_for_end();
   super.wait_for_end();
endtask: wait_for_end

task tb_env::cleanup();
   super.cleanup();
endtask: cleanup

task tb_env::report() ;
   super.report();
endtask: report

`endif // TB_ENV__SV
