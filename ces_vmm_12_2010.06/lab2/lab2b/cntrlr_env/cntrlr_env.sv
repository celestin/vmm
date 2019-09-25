`include "cpu_trans.sv"
`include "cpu_driver.sv"
// Lab 2b - Include the sram model and transaction files
// ToDo


// Lab 2b - Extend the env from vmm_group for implicitly phased env.
class cntrlr_env; // ToDo

   string     inst;
   cpu_driver drv;

   // Lab 2b - Declare an array of sram blocks
   // ToDo


   extern  function new(string inst, vmm_unit parent=null);

   // Lab 2b - change methods to implicit phase methods
   extern virtual task reset(); // ToDo
   extern virtual function void build(); // ToDo

   // Lab 2b - Delete the run() task
   extern virtual task run(); // ToDo

   // Lab 2b - Create the connect_ph() method
   // ToDo


endclass

function cntrlr_env::new(string inst, vmm_unit parent);
   super.new("cntrlr_env", inst, parent);
   this.inst = inst;
endfunction

// Lab 2b - Change the reset() task to the implicit phase method reset_ph()
task cntrlr_env::reset(); // ToDo
   // ToDo - Add log message for debugging

   test_top.reset <= 1'b0;
   repeat(1) @(test_top.cpuif.cb)
   test_top.reset <= 1'b1;
   repeat(10) @(test_top.cpuif.cb)
   test_top.reset <= 1'b0;
   // ToDo - Add log message for debugging

endtask

// Lab 2b - Change the build() task to the implicit phase method build_ph()
function void cntrlr_env::build(); // ToDo 
   drv      = new("CPUDrv", this, 5);

   // Lab 2b - Create 4 sram blocks and construct them
   // ToDo
   
endfunction

// Lab 2b - Delete the run() task.  Execution is now implicit with vmm_group.
task cntrlr_env::run(); // ToDo
   drv.main();
endtask

// Lab 2b - Create the connect_ph() method and register drv object with the
//          consensus object vote.
// ToDO



