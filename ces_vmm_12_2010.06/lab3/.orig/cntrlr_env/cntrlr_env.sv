`include "cpuport.sv"
`include "sramport.sv"
`include "cpu_trans.sv"
`include "cpu_driver.sv"
`include "sram_trans.sv"
`include "sram_model.sv"
`include "cpu_rand_scenario.sv"

class cntrlr_env extends vmm_group;
   `vmm_typename(cntrlr_env)

   // Lab 3 - Declare an instance of the multi-stream scenario gen
   // ToDo


   // Lab 3 - Declare an instance of the cpu_trans_channel
   // ToDo


   // Lab 3 - Declare an instance of the random scenario
   // ToDo


   sram_model rams[];
   cpu_driver drv;
   int        num_scenarios;
   int        timeout;

   //extern methods
   extern  function new(string name, vmm_unit parent=null);
   extern  virtual function void build_ph();
   extern  virtual function void connect_ph();
   extern  virtual function void start_of_sim_ph();
   extern  virtual task reset_ph();

endclass

function cntrlr_env::new(string name, vmm_unit parent);
   super.new("cntrlr_env", name, parent);
endfunction

function void cntrlr_env::build_ph();
   super.build_ph();
   `vmm_trace(log, "Building components...");

   // Lab 3 - Building the generator
   // ToDo

  
   // Lab 3 - Building the channel
   // ToDo


   drv = new("CPUDrv", this);   

   this.rams = new [4];
   for (int i=0; i<4; i++) begin
      this.rams[i] = new($psprintf("SRAM_%0d", i), this, i);
   end

   // Lab 3 - Construct the scenario object
   // ToDo

endfunction

function void cntrlr_env::connect_ph();
   super.connect_ph();
   // Lab 3 - register the channel with the MSS gen
   // ToDo


   // Lab 3 - register the rand scenario with MSS gen
   // ToDo


   // Lab 3 - connect the output chan of the generator to the input chan of the driver.
   // ToDo


   // Lab 3 - register the MSS gen's DONE event with the consensus object
   // ToDo


   // Register the driver object with the consensus object
   this.vote.register_xactor(this.drv);
endfunction

function void cntrlr_env::start_of_sim_ph();
   // Lab 3 - Create is_set variable to determine whether or not num_scenarios is set externally
   // ToDo


   super.start_of_sim_ph();

   // Lab 3 - Call vmm_opts::get_object_int() to receive the num_scenarios set from the test
   // ToDo


   // Lab 3 - Assign the stop_after_n_scenarios to restrict the transaction
   //         count. 'num_scenarios' can be modified using vmm_opts from the test.
   // ToDo

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
