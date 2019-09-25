`include "cpuport.sv"
`include "cpu_subenv.sv"
`include "memsys_trans.sv"
`include "memsys_scenario.sv"
`include "memsys_xactor.sv"

class memsys_env extends vmm_unit;
  // log handle
  vmm_log                          log;

  // cpu0 instance
  cpu_subenv                       cpu0;
  // cpu1 instance
  cpu_subenv                       cpu1;

  // top level scenario object
  memsys_scenario                  memsys_scn;

  // multi stream scenario generator handle
  //vmm_ms_scenario_gen            gen;

  // scenario generator object
  memsys_trans_scenario_gen        scn_gen;

  // consensus
  vmm_consensus                    end_vote;

  // memsys transaction channel
  memsys_trans_channel             genToXtr_chan;

  // memsys xactor object
  memsys_xactor                    mem_xtr;

  // num of scenarios
  int                              num_scenarios;

`vmm_unit_config_begin(memsys_env)
   `vmm_unit_config_rand_int(num_scenarios, 5, "runs number of scenarios", 0, "DO_ALL")
`vmm_unit_config_end(memsys_env)
  
  //extern methods
  extern  function new(string name, vmm_unit parent=null);
  extern  virtual function void build_ph();
  extern  virtual function void connect_ph();
  extern  virtual task reset_ph();
  extern  virtual task shutdown_ph();
  extern  virtual task run_ph();


endclass

function memsys_env::new(string name, vmm_unit parent);
  super.new(get_typename(), name, parent);
   log = new("memsys_env", "class");
   log.stop_after_n_errors(0); //Simulation doesnt stop for errors
endfunction


function void memsys_env::build_ph();

  `vmm_trace(log, "Building components...");

   //Building the components
   cpu0 = new("subenv", "CPU0", this);
   cpu1 = new("subenv", "CPU1", this);
   this.genToXtr_chan = new("Gen to Xtr chan","class");
   this.scn_gen = new("SCN_Gen",0,,this);
   memsys_scn = memsys_scenario::create_instance(scn_gen,"MEMSYS_SCN", `__FILE__, `__LINE__);
   this.scn_gen.scenario_set[0] = memsys_scn;
   vmm_opts::set_int("CPU0:enable_gen", 0, this);
   vmm_opts::set_int("CPU1:enable_gen", 0, this);
endfunction


function void memsys_env::connect_ph();
   this.mem_xtr = new ("memsys scheduler","xactor", this);
   mem_xtr.genToXtr_chan = scn_gen.out_chan;
   mem_xtr.xtrToCPU0Drv_chan = cpu0.gen_to_drv_chan;;
   mem_xtr.xtrToCPU1Drv_chan = cpu1.gen_to_drv_chan;;
   scn_gen.stop_after_n_scenarios = num_scenarios;
endfunction

task memsys_env::reset_ph();
  `vmm_verbose(this.log,"Resetting DUT...");
  test_top.reset <= 1'b0;
  repeat(1) @(test_top.port0.cb)
  test_top.reset <= 1'b1;
  repeat(10) @(test_top.port0.cb)
  test_top.reset <= 1'b0;
  `vmm_verbose(this.log,"RESET DONE...");
endtask


task memsys_env::shutdown_ph();
   scn_gen.stop_xactor();
endtask

task memsys_env::run_ph();
  scn_gen.notify.wait_for(cpu_trans_scenario_gen::DONE);
  `vmm_debug(this.log,"About to end simulation...");
endtask


