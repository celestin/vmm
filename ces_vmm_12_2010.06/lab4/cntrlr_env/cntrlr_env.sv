`include "cpuport.sv"
`include "sramport.sv"
`include "cpu_trans.sv"
`include "cpu_driver.sv"
`include "sram_trans.sv"
`include "sram_model.sv"
`include "cpu_rand_scenario.sv"

// Lab 4 - Include the scoreboard top file
// ToDo


// Lab 4 - Include the coverage class
// ToDo


// Lab 4 - Include the CPU coverage callback class
// ToDo


// Lab 4 - Include the SRAM coverage callback class
// ToDo


class cntrlr_env extends vmm_group;

   sram_model           rams[];

   // Declare an instance of the multi-stream scenario gen
   vmm_ms_scenario_gen  cpu_gen;

   //  Declare an instance of the cpu_trans_channel
   cpu_trans_channel    gen_out_chan;

   //  Declare an instance of the random scenario
   cpu_rand_scenario    rand_scn;

   cpu_driver           drv;

   // Lab 4 - Declare an instance of the scoreboard top class
   // ToDo 


   // Lab 4 - Declare an instance of the coverage class
   // ToDo 


   // Lab 4 - Declare an instance of the CPU coverage callback class
   // ToDO


   // Lab 4 - Declare an instance of the SRAM coverage callback class
   // ToDo


   int                  num_scenarios;
   int                  timeout;

   //extern methods
   extern  function new(string name, vmm_unit parent=null);
   extern  virtual function void build_ph();
   extern  virtual function void connect_ph();
   extern  virtual function void start_of_sim_ph();
   extern  virtual task reset_ph();
   extern  virtual task shutdown_ph();
   extern  virtual function void report_ph();

endclass

function cntrlr_env::new(string name, vmm_unit parent);
   super.new("cntrlr_env", name, parent);
endfunction

function void cntrlr_env::build_ph();
   super.build_ph(); 
   `vmm_trace(log, "Building components...");

   //  Building the generator
   cpu_gen = new("CPUGen",0, this);
  
   drv = new("CPUDrv", this);   
   this.gen_out_chan = new("GenOutChan", "cpu_chan");

   this.rams = new [4];
   for (int i=0; i<4; i++) begin
      string str = $psprintf("SRAM_%0d", i);
      this.rams[i] = new(str, this, i);
   end

   //  Construct the scenario object
   rand_scn = new();

   // Lab 4 - Construct the scoreboard top object
   // ToDo


   // Lab 4 - Construct the coverage object
   // ToDo


   // Lab 4 - Construct the CPU coverage callback object
   // ToDo


   // Lab 4 - Construct the SRAM coverage callback object
   // ToDo

endfunction

function void cntrlr_env::connect_ph();
   super.connect_ph();
   // Lab 4 - Bind the TLM exports to ports using tlm_bind
   // ToDo


   //  register the channel with the MSS gen
   this.cpu_gen.register_channel("cpu_chan", gen_out_chan);

   //  register the rand scenario with MSS gen
   this.cpu_gen.register_ms_scenario("rand_scn", rand_scn);

   //  register generator, driver and ram with the consensus object
   this.vote.register_xactor(cpu_gen);
   this.vote.register_xactor(drv);
   foreach (rams[i])
      this.vote.register_xactor(rams[i]);

   //  connect the output chan of the generator to the input chan of the driver.
   this.drv.in_chan      = this.gen_out_chan;

   // Lab 4 - Append the CPU coverage callback object with the CPU transactor
   // ToDo

	  
   // Lab 4 - Append the SRAM coverage callback object with the SRAM transactor
   // ToDo

endfunction

function void cntrlr_env::start_of_sim_ph();
   super.start_of_sim_ph();
   num_scenarios = 50;
   //  Assign the stop_after_n_scenarios to restrict the transaction
   //  count. 'num_scenarios' can be modified using vmm_opts from the test.
   this.cpu_gen.stop_after_n_scenarios = num_scenarios;
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

task cntrlr_env::shutdown_ph();
   super.shutdown_ph();
   // Lab 4 - Wait for the scoreboard to notify EMPTY before shutdown
   // ToDo

endtask

function void cntrlr_env::report_ph();
   super.report_ph();
   // Lab 4 - Call the scoreboard report task to output the scoreboard report
   // ToDo

endfunction
