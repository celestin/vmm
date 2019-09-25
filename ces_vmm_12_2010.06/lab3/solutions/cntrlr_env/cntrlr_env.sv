`include "cpuport.sv"
`include "sramport.sv"
`include "cpu_trans.sv"
`include "cpu_driver.sv"
`include "sram_trans.sv"
`include "sram_model.sv"
`include "cpu_rand_scenario.sv"

class cntrlr_env extends vmm_group;

   sram_model           rams[];

   // Lab 3 - Declare an instance of the multi-stream scenario gen
   vmm_ms_scenario_gen  cpu_gen;

   // Lab 3 - Declare an instance of the cpu_trans_channel
   cpu_trans_channel    gen_out_chan;

   // Lab 3 - Declare an instance of the random scenario
   cpu_rand_scenario    rand_scn;

   cpu_driver           drv;
   int                  num_scenarios;

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
 
   `vmm_trace(log, "Building components...");

   // Lab 3 - Building the generator
   cpu_gen = new("CPUGen",0, this);
  
   drv = new("CPUDrv", this);   
   this.gen_out_chan = new("GenOutChan", "cpu_chan");

   this.rams = new [4];
   for (int i=0; i<4; i++) begin
      string str = $psprintf("SRAM_%0d", i);
      this.rams[i] = new(str, this, i);
   end

   // Lab 3 - Construct the scenario object
   rand_scn = new();
endfunction

function void cntrlr_env::connect_ph();
   vote.register_xactor(cpu_gen);
   vote.register_xactor(drv);
   foreach (rams[i])
      vote.register_xactor(rams[i]);
   // Lab 3 - register the channel with the MSS gen
   this.cpu_gen.register_channel("cpu_chan", gen_out_chan);

   // Lab 3 - register the rand scenario with MSS gen
   this.cpu_gen.register_ms_scenario("rand_scn", rand_scn);

   // Lab 3 - register the MSS gen's DONE event with the voter class
   this.vote.register_notification(this.cpu_gen.notify, vmm_ms_scenario_gen::DONE);

   // Lab 3 - connect the output chan of the generator to the input chan of the driver.
   this.drv.in_chan      = this.gen_out_chan;
endfunction

function void cntrlr_env::start_of_sim_ph();
   bit is_set;
   // Lab 3 - Assign the stop_after_n_scenarios to restrict the transaction
   //         count. 'num_scenarios' can be modified using vmm_opts from the test.

   // Lab 3 - Call vmm_opts::get_object_int() to receive the num_scenarios from the test
   num_scenarios = vmm_opts::get_object_int(is_set, this, "num_scenarios", 5);

   // Lab 3 - Set the generator's stop_after_n_scenarios with the value of num_scenarios
   this.cpu_gen.stop_after_n_scenarios = num_scenarios;
endfunction

task cntrlr_env::reset_ph();
   `vmm_verbose(this.log,"Resetting DUT...");
   test_top.reset <= 1'b0;
   repeat(1) @(test_top.cpuif.cb)
   test_top.reset <= 1'b1;
   repeat(10) @(test_top.cpuif.cb)
   test_top.reset <= 1'b0;
   `vmm_verbose(this.log,"RESET DONE...");
endtask
