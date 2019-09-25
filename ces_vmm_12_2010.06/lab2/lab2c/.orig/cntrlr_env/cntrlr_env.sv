`include "cpu_trans.sv"
`include "cpu_driver.sv"
`include "sram_trans.sv"
`include "sram_model.sv"

class cntrlr_env extends vmm_group;

   string                 inst;
   cpu_driver             drv;
   sram_model             rams[];

   extern function new(string inst, vmm_unit parent=null);
   extern virtual task reset_ph();
   extern virtual function void build_ph();
   extern virtual task run_ph();

endclass

function cntrlr_env::new(string inst, vmm_unit parent);
   super.new("cntrlr_env", inst, parent);
   this.inst = inst;
endfunction

task cntrlr_env::reset_ph();
   super.reset_ph();
   `vmm_verbose(this.log,"Resetting DUT...");
   test_top.reset <= 1'b0;
   repeat(1) @(test_top.cpuif.cb)
   test_top.reset <= 1'b1;
   repeat(10) @(test_top.cpuif.cb)
   test_top.reset <= 1'b0;
   `vmm_verbose(this.log,"RESET DONE...");
endtask

function void cntrlr_env::build_ph();
   super.build_ph();
   drv  = new("CPUDrv", this, 5);
   rams = new[4];
   foreach(rams[i])
      rams[i]  = new("rams", this, i);
endfunction

task cntrlr_env::run_ph();
   super.run_ph();
   vote.register_xactor(drv);
endtask
