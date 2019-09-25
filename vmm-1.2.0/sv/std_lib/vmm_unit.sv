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
function vmm_unit::new(string name,
             string inst,
             vmm_object parent = null);
   vmm_unit unit_obj;
   super.new(parent, inst);      
   this.log = new(this.get_typename(), inst);
   this.enable_unit = 1;
   this.vote = new(inst, $psprintf("%s",inst));
   if($cast(unit_obj,parent) && parent!=null)
      unit_obj.vote.register_consensus(this.vote);
   this.voter  = this.vote.register_voter(this.get_object_hiername());
   this.voter.consent("consent by default ");
endfunction:new

function bit vmm_unit::is_unit_enabled();
  return this.enable_unit;
endfunction:is_unit_enabled

function void vmm_unit::set_parent_object(vmm_object parent);
   vmm_unit unit_obj;
   $cast(unit_obj,this.get_parent_object());
   if(unit_obj!=null) begin
      unit_obj.vote.unregister_consensus(this.vote);
   end
   super.set_parent_object(parent);
   if($cast(unit_obj,parent) && parent!=null)
      unit_obj.vote.register_consensus(this.vote);
endfunction:set_parent_object

function void vmm_unit::consent(string why);
      this.voter.consent(why);
endfunction:consent

function void vmm_unit::oppose(string why);
      this.voter.oppose(why);
endfunction:oppose

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

   // Find the nearest-enclosing timeline
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

function void vmm_unit::build_ph();
endfunction:build_ph

function void vmm_unit::configure_ph();
endfunction:configure_ph

function void vmm_unit::connect_ph();
endfunction:connect_ph

function void vmm_unit::start_of_sim_ph();
endfunction:start_of_sim_ph

task vmm_unit::disabled_ph();
endtask:disabled_ph

task vmm_unit::reset_ph();
endtask:reset_ph

task vmm_unit::training_ph();
endtask:training_ph

task vmm_unit::config_dut_ph();
endtask:config_dut_ph

task vmm_unit::start_ph();
endtask:start_ph

function void vmm_unit::start_of_test_ph();
endfunction:start_of_test_ph

task vmm_unit::run_ph();
endtask:run_ph

task vmm_unit::shutdown_ph();
endtask:shutdown_ph

task vmm_unit::cleanup_ph();
endtask

function void vmm_unit::report_ph();
endfunction:report_ph

function void vmm_unit::destruct_ph();
endfunction:destruct_ph


