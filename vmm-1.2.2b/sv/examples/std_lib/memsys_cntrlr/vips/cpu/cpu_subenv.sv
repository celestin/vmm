//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

`include "cpuport.sv"
`include "cpu_trans.sv"
`include "cpu_config.sv"
`include "cpu_driver.sv"
`include "cpu_scenario_lib.sv"

class cpu_subenv extends vmm_group;
  `vmm_typename(cpu_subenv)

  typedef enum bit [1:0] {NORMAL, RECORD, PLAYBACK} mode_e;

  cpu_config                 cfg;
  // driver instance
  cpu_driver                 drv;
  vmm_ms_scenario_gen        gen;
  cpu_trans_channel          gen_to_drv_chan;

  //Scenarios
  cpu_rand_scenario          rand_scn;

  bit                        enable_gen;
  rand int                   num_scenarios;
  mode_e                     mode = NORMAL;

  extern function new(string inst, 
                      vmm_unit parent=null);
  extern virtual function void build_ph();
  extern virtual function void configure_ph();
  extern virtual function void connect_ph();
  extern virtual function void start_of_sim_ph();
  extern virtual task run_ph();
  extern virtual task shutdown_ph();
  extern virtual task cleanup_ph();
endclass

/*******************************************************************************
  new() :  constructor
*******************************************************************************/
function cpu_subenv::new(string inst, vmm_unit parent);
  super.new(get_typename(), inst, parent);
endfunction

/*******************************************************************************
  build_ph() :  build components
*******************************************************************************/
function void cpu_subenv::build_ph();
   int is_set;
   $cast(this.cfg,vmm_opts::get_object_obj(is_set,this,"cpu_cfg"));
   if(this.cfg == null) `vmm_fatal(log,"Null Configuration returned for CPU subenv");
  
    this.drv = cpu_driver::create_instance(this, {get_object_name(), "Drv"}, `__FILE__, `__LINE__); 
   this.gen = new({get_object_name(), "Gen"},0, this);
   this.gen_to_drv_chan = new("Gen2DrvChan", "cpu_chan");

endfunction

/*******************************************************************************
  configure_ph() :  configure components
*******************************************************************************/

function void cpu_subenv::configure_ph();
   string MODE;
   `vmm_unit_config_int(enable_gen, 1, "Enables/disables the scenario generator", 0, DO_ALL)
   `vmm_unit_config_string(MODE, "NORMAL", "Specifies the mode NORMAL/RECORD/PLAYBACK", 0, DO_ALL)
   case (MODE)
     "NORMAL"   : mode = NORMAL;
     "RECORD"   : mode = RECORD;
     "PLAYBACK" : begin
                   mode = PLAYBACK;
                   enable_gen = 0;
                  end
   endcase

endfunction

/*******************************************************************************
  connect_ph() :  connect components
*******************************************************************************/
function void cpu_subenv::connect_ph();
   this.drv.in_chan = this.gen_to_drv_chan;
   if (enable_gen) begin
      this.gen.register_channel("cpu_chan", gen_to_drv_chan);
      this.vote.register_notification(this.gen.notify, vmm_ms_scenario_gen::DONE);

      if (mode == RECORD) begin
         this.gen_to_drv_chan.record({"Channel_", get_object_name(), ".dat"});
      end
   end
   else begin
      this.gen.disable_unit();
   end
endfunction

/*******************************************************************************
  start_of_sim_ph() : Setting generator parameters
*******************************************************************************/
function void cpu_subenv::start_of_sim_ph();
   `vmm_unit_config_rand_int(num_scenarios, 1, "runs number of scenarios", 0, DO_ALL)
   void'(this.randomize());
   if (!enable_gen) return;
   this.gen.stop_after_n_scenarios = num_scenarios;
   rand_scn = cpu_rand_scenario::create_instance(this, "rand_scn", `__FILE__, `__LINE__);
   this.gen.register_ms_scenario("rand_scn", rand_scn);
endfunction

/*******************************************************************************
  run_ph() :  Execute main operation
*******************************************************************************/
task cpu_subenv::run_ph();
   if (mode == PLAYBACK) begin
      bit success;
      cpu_trans tr = new;
      this.gen_to_drv_chan.playback(success, {"Channel_", get_object_name(), ".dat"}, tr);
      if (!success) begin
         `vmm_fatal(log, "Playback mode failed for channel");
      end
   end
endtask

/*******************************************************************************
  shutdown_ph() :  transactors are stopped
*******************************************************************************/
task cpu_subenv::shutdown_ph();
   if(enable_gen) gen.stop_xactor();
   drv.stop_xactor();
   `vmm_trace(log, "generator stopped");
endtask

/*******************************************************************************
  cleanup_ph() :  cleaning up scenarios, channels (if needed for concatenation)
*******************************************************************************/
task cpu_subenv::cleanup_ph();
   if(enable_gen) begin
      gen.unregister_ms_scenario(rand_scn);
      gen.reset_xactor();
   end
endtask


