`include "cpu_trans.sv"
`include "cpu_driver.sv"
`include "cpu_scenario.sv"

class cpu_subenv extends vmm_unit;

  // driver instance
  cpu_driver                 drv;

  // generator instance
  cpu_trans_scenario_gen    gen;

  // scenario handle
  cpu_scenario               scn;

  // generator to driver channel
  cpu_trans_channel          gen_to_drv_chan;

  // transaction blueprint;
  cpu_trans                  blueprint;

  // driver callback instance
  cpu_driver_callbacks       drv_cb;

  // instance name
  string                     inst_name;


  bit                        enable_gen;

`vmm_unit_config_begin(memsys_env)
   `vmm_unit_config_int(enable_gen, 1, "Enables/disables the scenario generator", 0, DO_ALL)
`vmm_unit_config_end(memsys_env)


  extern function new(string name, string inst, 
                      vmm_unit parent=null);
  extern virtual function void build_ph();
  extern virtual function void connect_ph();
  extern virtual task shutdown_ph();
endclass

/*******************************************************************************
  new() :  constructor
*******************************************************************************/
function cpu_subenv::new(string name, string inst, vmm_unit parent);
  super.new(name, inst, parent);
  this.inst_name = inst;
endfunction

/*******************************************************************************
  build_ph() :  build components
*******************************************************************************/
function void cpu_subenv::build_ph();
   this.scn = new();
   this.gen_to_drv_chan = new("Gen2DrvChan", {inst_name, "Chan"});
   this.drv = new("CpuDriver", "Drv", this);
   this.gen = new({inst_name, "Gen"},0);
   this.gen.scenario_set[0] = scn;
endfunction

/*******************************************************************************
  connect_ph() :  connect components
*******************************************************************************/
function void cpu_subenv::connect_ph();
   this.gen.out_chan = this.gen_to_drv_chan;
   this.drv.in_chan = this.gen_to_drv_chan;
endfunction

/*******************************************************************************
  shutdown_ph() :  transactors are stopped
*******************************************************************************/
task cpu_subenv::shutdown_ph();
   if (enable_gen) gen.stop_xactor();
   `vmm_trace(log, "generator stopped");
endtask


