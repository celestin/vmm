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

// //////////////////////////////////////////// 
//
// Class: vmm_unit
//
// Base class for providing pre-defined simulation phases.
// 
// This class is used as the base class that provides pre-defined simulation phases to 
// structural elements, such as transactors, transaction-level models and generators. 
// 
// The purpose of this class is to:
//   - Support structural composition and connectivity.
//   - Integrate into a simulation timeline.
//
// The vmm_unit class should not be directly extended. Instead, vmm_xactor and vmm_group 
// are extended from vmm_unit.
//
// Since the vmm_xactor and vmm_group base classes are extended from vmm_unit, all classes 
// extended from these base classes can invoke the phase methods. You should continue to 
// extend vmm_xactor for implementing transactors, and for implementing compositions 
// (combination of components), extend vmm_group.
// 
// The following are the phases, listed in the order in which they are called:
//   - <build_ph>
//   - <configure_ph>
//   - <connect_ph>
//   - <configure_test_ph>
//   - <start_of_sim_ph>
//   - <reset_ph>
//   - <training_ph>
//   - <config_dut_ph>
//   - <start_ph>
//   - <start_of_test_ph>
//   - <run_ph>
//   - <shutdown_ph>
//   - <cleanup_ph>
//   - <report_ph>
//   - <final_ph>
  
// //////////////////////////////////////////// 
// Function: new 
// 
// Constructs an instance of this class with the specified name, instance name, and optional
// parent. 
// The specified name is used as the name of the embedded vmm_log. The specified instance
// name is used as the name of the underlying vmm_object. 
// 
//|   class vip1 extends vmm_group;
//|      function new (string name, string inst);
//|         super.new (this,inst);
//|      endfunction
//|   endclass
function vmm_unit::new(string name,
             string inst,
             vmm_object parent = null);
   vmm_unit unit_obj;
   vmm_object vmm_obj;
   string safe_name;
   super.new(parent, inst);      
   safe_name = (name == "") ? "vmm_unit" : name;
   hier_inst = super.get_object_hiername();
   this.log = new(name, get_object_hiername());
   this.enable_unit = 1;
   this.vote = new({safe_name, ".consensus"}, {inst,".vote"}, this.log);
   if ($cast(vmm_obj, this.vote)) vmm_obj.set_parent_object(this);
   this.voter  = this.vote.register_voter(this.get_object_hiername());
   if (vmm_consensus::is_register_consensus()) begin
     if($cast(unit_obj,parent) && (parent!=null))
        unit_obj.vote.register_consensus(this.vote);
     this.voter.consent("consent by default ");
   end
endfunction:new

function bit vmm_unit::is_unit_enabled();
  return this.enable_unit;
endfunction:is_unit_enabled

function void vmm_unit::set_parent_object(vmm_object parent);
   vmm_unit unit_obj;
   $cast(unit_obj,this.get_parent_object());
   if(unit_obj!=null && vmm_consensus::is_register_consensus()) begin
      unit_obj.vote.unregister_consensus(this.vote);
   end
   super.set_parent_object(parent);
   hier_inst = super.get_object_hiername();
   this.log.set_instance( this.get_object_hiername());
   if($cast(unit_obj,parent) && parent!=null  && vmm_consensus::is_register_consensus())
      unit_obj.vote.register_consensus(this.vote);
endfunction:set_parent_object

function string vmm_unit::get_object_hiername(vmm_object root = null, string space = "");
   return hier_inst;
endfunction:get_object_hiername

// //////////////////////////////////////////// 
// Function: consent 
// 
// Expresses the consents of this vmm_unit to the consensus for the specified reason.
// 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      task reset_ph();
//|         this.oppose("reset phase running");
//|         fork
//|            begin
//|               #50;
//|               this.consent("reset phase finished");
//|            end
//|         join_none
//|      endtask:reset_ph
//|      ...
//|   endclass
function void vmm_unit::consent(string why="No reason specified");
      this.voter.consent(why);
endfunction: consent

// //////////////////////////////////////////// 
// Function: oppose 
// 
// Overrides the specified phase with the specified phase definition for this instance.
// If def is null, the override (if any) is removed. Returns the previous override phase
// definition (if any). 
// 
//|   class cust_configure_phase_def #(type T = groupExtension)       extends vmm_topdown_function_phase_def #(T);
//|      function void do_function_phase( T obj);
//|         obj.cust_config_ph();
//|      endfunction
//|   endclass
//|   
//|   class groupExtension extends vmm_group;
//|      function void config_ph();
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::configure_ph"));
//|       endfunction:config_ph
//|      function void cust_config_ph();
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::cust_config_ph"));
//|      endfunction:cust_config_ph
//|   endclass
//|   
//|   cust_configure_phase_def  cust_cfg = new();
//|   groupExtension   m1 = new("groupExtension","m1");
//|   `void(m1.override_phase("configure",cust_cfg ));
function void vmm_unit::oppose(string why="No reason specified");
      this.voter.oppose(why);
endfunction: oppose

// //////////////////////////////////////////// 
// Function: forced 
// 
// Forces consensus for this unit to be reached. The consensus may be subsequently consented
// to by calling the <consent() method, or it may be opposed by calling the oppose>
// method. 
// The forcing of consensus through the parent unit occurs, only if this unit is configured
// to force through to its parent by the <force_thru> method. The why argument
// is a string that specifies the reason why the consensus is forced on this unit. 
// 
function void vmm_unit::forced(string why="No reason specified");
      this.voter.forced(why);
endfunction: forced

// //////////////////////////////////////////// 
// Function: force_thru 
// 
// Checks if this vmm_unit instance is disabled or not. By default, all units are enabled.
// A unit may be disabled by calling its disable_unit() method, before the start_of_sim
// phase. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|   endclass
//|   
//|   class udf_start_def extends vmm_fork_task_phase_def 
//|         #(groupExtension);
//|      ...
//|      task do_task_phase(groupExtension obj);
//|         if(obj.is_unit_enabled())
//|            obj.udf_start_ph();
//|      endtask:do_task_phase
//|      ...
//|   endclass
function void vmm_unit::force_thru(vmm_unit child,
                                        bit      thru = 1);
      this.vote.consensus_force_thru(child.vote, thru);
endfunction: force_thru

// //////////////////////////////////////////// 
// 
// Task: request_consensus 
// 
// Makes a request of all currently-opposing participants in this unit instance that
// they consent to the consensus. 
// A request is made by calling the <consensus_requested> method in this unit,
// and all currently-opposing child units. If a forced consensus on this unit forces through
// to a higher-level unit, then the consensus request is propagated upward as well. This
// task returns when the local unit-level consensus is reached. 
// The why argument is a string that specifies the reason why the consensus is forced on
// this unit. 
// 
// 
task vmm_unit::request_consensus(string why="No reason specified");
      this.voter.request(why);
endtask: request_consensus

// //////////////////////////////////////////// 
// Function: consensus_requested 
// 
// When this method is called, it indicates that a consensus request is made to this currently-opposing
// unit by the specified unit, by calling the <request_consensus> method.
// 
// This method should be extended, if this unit is to honor consensus requests. 
// 
function void vmm_unit::consensus_requested(vmm_unit who);
endfunction: consensus_requested

function void vmm_unit::disable_child_unit(vmm_object obj);
   vmm_unit mod;
   vmm_object child;
   int i;

      i = 0;
      child = obj.get_nth_child(i++);
      while (child != null) begin
         if ($cast(mod, child)) begin
	        mod.enable_unit=0;
            this.disable_child_unit(mod);
         end
         else this.disable_child_unit(child);
         child = obj.get_nth_child(i++);
      end
endfunction:disable_child_unit

// //////////////////////////////////////////// 
// Function: disable_unit 
// 
// Disables this instance of the vmm_unit class. This method must be called, before the
// start_of_sim phase. A vmm_unit instance can only be re-enabled by resetting its timeline
// to the configure phase or earlier. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|   endclass
//|   
//|   groupExtension m1 = new ("groupExtension","m1");
//|   m1.disable_unit();
function void vmm_unit::disable_unit();
   vmm_timeline tl;
   tl = this.get_timeline();
   if(tl==null)
	  `vmm_warning(this.log,`vmm_sformatf( "No timeline available for %s(%s) , hence can't be disabled ",this.get_object_name(),this.get_typename()));
   else begin
      int start_of_sim_ph_idx ;
      int current_ph_idx ;
	  current_ph_idx = tl.get_current_phase_index();
	  start_of_sim_ph_idx = tl.get_phase_index("start_of_sim");
	  if(current_ph_idx < start_of_sim_ph_idx) begin
	     this.enable_unit = 0;
		 disable_child_unit(this);
	  end
	  else
		 `vmm_warning(this.log,`vmm_sformatf( "%s(%s) can be disabled only before \"start_of_sim\" phase , hence ignoring disabling unit",this.get_object_name(),this.get_typename()));  
   end
endfunction:disable_unit

function vmm_timeline vmm_unit::get_timeline();
   // Start with the parent in case this is itself a timeline
   vmm_object parent = this.get_parent_object();
   get_timeline = null;
   while (parent != null) begin
      if ($cast(get_timeline, parent)) break;
      parent = parent.get_parent_object();
   end
   if (get_timeline == null) begin
      get_timeline = vmm_simulation::get_top_timeline();
   end
endfunction:get_timeline

function vmm_phase_def vmm_unit::override_phase(string name, vmm_phase_def def);
   if (this.override_phase_defs.exists(name)) begin
      override_phase = this.override_phase_defs[name];
      if(def==null) begin
         this.override_phase_defs.delete(name);
		 return override_phase;
      end
   end
   override_phase_defs[name] = def;
endfunction:override_phase

// //////////////////////////////////////////// 
// Function: build_ph 
// 
// Builds testbench components
function void vmm_unit::build_ph();
endfunction:build_ph

// //////////////////////////////////////////// 
// Function: configure_ph 
// 
// Configures the testbench components
function void vmm_unit::configure_ph();
endfunction:configure_ph

// //////////////////////////////////////////// 
// Function: connect_ph 
// 
// Connects the interfaces that are wholly contained within this component. 
// 
//|   class memsys_env extends vmm_group;
//|      cpu_subenv extends cpu0;
//|      vmm_ms_scenario_gen gen;
//|      memsys_scenario memsys_scn;
//|      ... 
//|      function void build_ph();
//|         cpu0 = new("subenv", "CPU0", this);
//|         cpu1 = new("subenv", "CPU1", this);
//|         memsys_scn = new();
//|         gen = new("MS-Generator");
//|         ...
//|      endfunction
//|   
//|      function void memsys_env::connect_ph;
//|         gen.register_channel("cpu0_chan", 
//|            cpu0.gen_to_drv_chan);
//|         gen.register_channel("cpu1_chan",
//|            cpu1.gen_to_drv_chan);
//|         gen.register_ms_scenario( "memsys_scn", memsys_scn);
//|         ...
//|      endfunction
//|   endclass
function void vmm_unit::connect_ph();
endfunction:connect_ph

// //////////////////////////////////////////// 
// Function: configure_test_ph 
// 
// Configures the test paramenters, options and factories
// 
function void vmm_unit::configure_test_ph();
endfunction:configure_test_ph

// //////////////////////////////////////////// 
// Function: start_of_sim_ph 
// 
// Static start of simulation
// 
function void vmm_unit::start_of_sim_ph();
endfunction:start_of_sim_ph

// //////////////////////////////////////////// 
// 
// Task: disabled_ph 
// 
// This Method gets executed instead of the reset_ph() method, if this vmm_unit instance
// is disabled. 
// 
//|   class groupExtension extends vmm_group;
//|      function void disabled_ph();
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::disabled_ph"));
//|         ...
//|      endfunction:disabled_ph
//|   endclass
task vmm_unit::disabled_ph();
endtask:disabled_ph

// //////////////////////////////////////////// 
// 
// Task: reset_ph 
// 
// Resets this unit, if it is enabled. This method is executed at the reset phase. 
// 
//|   class memsys_env extends vmm_group;
//|      task reset_ph();
//|         // Resetting the DUT
//|         test_top.reset <= 1'b0;
//|         repeat(1) @(test_top.port0.cb)
//|         test_top.reset <= 1'b1;
//|         repeat(10) @(test_top.port0.cb)
//|         test_top.reset <= 1'b0;
//|         `vmm_verbose(this.log,"RESET DONE...");
//|      endtask
//|   endclass
task vmm_unit::reset_ph();
endtask:reset_ph

// //////////////////////////////////////////// 
// Task: training_ph 
// 
// Waits for the DUT training to be complete
task vmm_unit::training_ph();
endtask:training_ph

// //////////////////////////////////////////// 
// Function: config_dut_ph 
// 
// Functional configuration of this component. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void configure_ph();
//|         `vmm_note  
//|         (log,`vmm_sformatf("groupExtension::configure_ph"));
//|         ...
//|      endfunction:configure_ph
//|   endclass
task vmm_unit::config_dut_ph();
endtask:config_dut_ph

// //////////////////////////////////////////// 
// 
// Task: start_ph 
// 
// Method to start processes within this component, if it is enabled. 
// 
//|   class memsys_env extends vmm_group;
//|      ...
//|      task start_ph();
//|         this.gen.start_xactor();
//|      endtask
//|      ...
//|   endclass
task vmm_unit::start_ph();
endtask:start_ph

// //////////////////////////////////////////// 
// Function: start_of_test_ph 
// 
// Method called at start of the test body, if it is enabled. 
// 
//|   class groupExtension extends vmm_group;
//|      function void start_of_test_ph();
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::start_of_test_ph"));
//|         ...
//|      endfunction:start_of_test_ph
//|   endclass
function void vmm_unit::start_of_test_ph();
endfunction:start_of_test_ph

// //////////////////////////////////////////// 
// 
// Task: run_ph 
// 
// Body of test, if it is enabled. Can be interrupted by resetting this component. May be
// stopped. 
// 
//|   class groupExtension extends vmm_group;
//|      task run_ph(); 
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::run_test_ph"));
//|         ...
//|      endtask : run_ph
//|   endclass
task vmm_unit::run_ph();
endtask:run_ph

// //////////////////////////////////////////// 
// Function: shutdown_ph 
// 
// Method called at start of the simulation. 
// 
//|   class cpu_driver extends vmm_group;
//|      ...
//|      function void start_of_sim_ph();
//|         if (iport == null)
//|            `vmm_fatal(log, "Virtual port not connected to the 
//|               actual interface instance");
//|      endfunction
//|      ...
//|   endclass
task vmm_unit::shutdown_ph();
endtask:shutdown_ph

// //////////////////////////////////////////// 
// 
// Task: cleanup_ph 
// 
// Method to perform post-execution verification, if it is enabled. 
// 
//|   class groupExtension extends vmm_group;
//|      task cleanup_ph(); 
//|         `vmm_note(log,`vmm_sformatf(
//|            "groupExtension::cleanup_ph"));
//|         ...
//|      endtask:cleanup_ph
//|   endclass
task vmm_unit::cleanup_ph();
endtask

// //////////////////////////////////////////// 
// Function: report_ph 
// 
// Method to perform post-test pass or fail reporting, if it is enabled. 
// 
//|   class memsys_env extends vmm_group;
//|      function void report_ph();
//|         sb.report;
//|         ...
//|      endfunction
//|   endclass
function void vmm_unit::report_ph();
endfunction:report_ph

// //////////////////////////////////////////// 
// Function: final_ph 
// 
// In case of multiple concatenated tests, final phase can be used to summarize the final
// report. 
// 
//|   class testExtension extends vmm_test;
//|   .
//|     function void final_ph();
//|       env.summary();
//|     endfunction
//|   
//|   endclass
function void vmm_unit::final_ph();
endfunction:final_ph

function void vmm_unit::set_object_name(string name="", string space="");
   super.set_object_name(name, space);
   log.set_instance(name);
endfunction

