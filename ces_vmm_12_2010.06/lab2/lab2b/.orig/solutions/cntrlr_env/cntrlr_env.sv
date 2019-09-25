`include "cpu_trans.sv"
`include "cpu_driver.sv"

// Lab 2b - Include the sram model and transaction files
`include "sram_trans.sv"
`include "sram_model.sv"

// Lab 2b - Extend the env from vmm_group for implicitly phased env.
class cntrlr_env extends vmm_group;

   string     inst;
   cpu_driver drv;

   // Lab 2b - Declare an array of sram blocks
   sram_model rams[];

   extern function new(string inst, vmm_unit parent=null);
   extern virtual task reset_ph();
   extern virtual function void build_ph();
   extern virtual function void connect_ph();

endclass

function cntrlr_env::new(string inst, vmm_unit parent);
   super.new("cntrlr_env", inst, parent);
   this.inst = inst;
endfunction

// Lab 2b - Change the reset() task to the in-built phase reset_ph()
task cntrlr_env::reset_ph();
    `vmm_verbose(this.log,"Resetting DUT...");
   test_top.reset <= 1'b0;
   repeat(1) @(test_top.cpuif.cb)
   test_top.reset <= 1'b1;
   repeat(10) @(test_top.cpuif.cb)
   test_top.reset <= 1'b0;
   `vmm_verbose(this.log,"RESET DONE...");
endtask

// Lab 2b - Change the build() task to the in-built phase build_ph()
function void cntrlr_env::build_ph();
   drv      = new("CPUDrv", this, 5);

   // Lab 2b - Create 4 sram blocks and construct them
   rams      = new[4];
   
   foreach(rams[i])
      rams[i]  = new($psprintf("ram_%0d", i), this, i);
endfunction

function void cntrlr_env::connect_ph();
   //  Lab 2b - register driver for consensus to end simulation
   vote.register_xactor(drv);
endfunction
