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

function vmm_phase::new(string name, 
                        vmm_timeline parent = null);
   super.new(parent, (name==""? this.get_typename():name));
endfunction:new

function string vmm_phase::get_name();
   return this.get_object_name();
endfunction:get_name

function vmm_timeline vmm_phase::get_timeline();
   $cast(get_timeline, this.get_parent_object());
endfunction:get_timeline

function vmm_phase vmm_phase::previous_phase();
   vmm_timeline tl = this.get_timeline();
   string ph = tl.get_previous_phase_name(this.get_object_name());
   return tl.get_phase(ph);
endfunction:previous_phase

function vmm_phase vmm_phase::next_phase();
   vmm_timeline tl = this.get_timeline();
   string ph = tl.get_next_phase_name(this.get_object_name());
   return tl.get_phase(ph);
endfunction:next_phase

function void vmm_phase::set_running();
  -> this.started;
  running = 1;
endfunction:set_running


function void vmm_phase::reset_running();
  -> this.completed;
  this.running = 0;
  this.phase_done = 1;
  this.done_count++;
  this.timeout_done = 0;
  this.abort_done = 0;
endfunction:reset_running

function bit vmm_phase::is_running();
   return this.running;
endfunction:is_running

function bit vmm_phase::is_phase_done();
   return this.phase_done;
endfunction:is_phase_done

function int vmm_phase::is_done();
   return this.done_count;
endfunction:is_done

function void vmm_phase::reset_done();
   this.phase_done = 0;
endfunction:reset_done

function int vmm_phase::is_aborted();
   return this.abort_count;
endfunction:is_aborted

function int vmm_phase::is_skipped();
   return this.skipped_count;
endfunction:is_skipped

function int vmm_timeline::get_current_phase_index();
   return (this.current_phase);
endfunction:get_current_phase_index

function int vmm_timeline::get_phase_index(string name);
   foreach (this.phases[i]) begin
      if (this.phases[i] == name) 
	     return i;
   end
endfunction:get_phase_index

////////////////////////////////////////////////////////////
// Class: vmm_timeline
//
// The vmm_timeline user-defined class coordinates simulation 
// through a user-defined timeline, with predefined test phases
// as defined in <vmm_unit>

////////////////////////////////////////////////////////////
// Function: new
// Creates an instance of the timeline base class, with the specified name, 
// instance name, and optional parent object.
//
function vmm_timeline::new(string name = "", 
                           string inst = "",
			   vmm_object parent = null);
   super.new((name==""? this.get_typename():name),inst, parent);
   `ifdef VMM_SV_SC_INTEROP // [[
      cont_execute_interop = 0;
   `endif // ]]   

   // Pre-defined run-time phases
   begin
      vmm_rtl_config_phase_def           rtl_config_ph      = new;
      vmm_unit_buildph_phase_def         build_ph           = new;
      vmm_unit_configph_phase_def        config_ph          = new;
      vmm_unit_connectph_phase_def       connect_ph         = new;
      vmm_unit_configtestph_phase_def    config_test_ph     = new;
      vmm_unit_startsimph_phase_def      startsim_ph        = new;
      vmm_unit_resetph_phase_def         reset_ph           = new;
      vmm_unit_trainingph_phase_def      training_ph        = new;
      vmm_unit_configdut_phase_def       configdut_ph       = new;
      vmm_unit_startph_phase_def         start_ph           = new; 
      vmm_unit_starttestph_phase_def     starttest_ph       = new;
      vmm_unit_run_testph_phase_def      run_test_ph        = new;
      vmm_unit_shutdownph_phase_def      shutdown_ph        = new;
      vmm_unit_cleanupph_phase_def       cleanup_ph         = new;
      vmm_unit_reportph_phase_def        report_ph          = new;
      vmm_unit_finalph_phase_def         final_ph           = new;


      void'(this.insert_phase_internal("rtl_config",      "$", rtl_config_ph));
      void'(this.insert_phase_internal("build",           "$", build_ph));
      void'(this.insert_phase_internal("configure",       "$", config_ph));
      void'(this.insert_phase_internal("connect",         "$", connect_ph));
      void'(this.insert_phase_internal("configure_test",  "$", config_test_ph));
      void'(this.insert_phase_internal("start_of_sim",    "$", startsim_ph));
      void'(this.insert_phase_internal("reset",           "$", reset_ph));
      void'(this.insert_phase_internal("training",        "$", training_ph));
      void'(this.insert_phase_internal("config_dut",      "$", configdut_ph));
      void'(this.insert_phase_internal("start",           "$", start_ph));
      void'(this.insert_phase_internal("start_of_test",   "$", starttest_ph));
      void'(this.insert_phase_internal("run_test",        "$", run_test_ph));
      void'(this.insert_phase_internal("shutdown",        "$", shutdown_ph));
      void'(this.insert_phase_internal("cleanup",         "$", cleanup_ph));
      void'(this.insert_phase_internal("report",          "$", report_ph));
      void'(this.insert_phase_internal("final",           "$", final_ph));
   end
`ifdef VMM_TR_RECORD
   this.top_stream = vmm_tr_record::open_stream(this.get_object_name(), "Timeline", vmm_debug::TRACE_SEV);
`endif //VMM_TR_RECORD
endfunction:new

// //////////////////////////////////////////// 
// Function: prepend_callback 
// 
// Renames the specified phase old_name in this timeline, to the new phase name new_name.
// Returns false, if the original named phase does not exist, or if a phase already exists
// with the new name. Generates a warning that a phase is renamed. Renaming timeline default
// phases is not allowed. The fname and lineno arguments are used to track the file name
// and the line number where this method is invoked from. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void build_ph ();
//|         vmm_timeline t = this.get_timeline();
//|         ...
//|         // Renaming predefined phase 'start_of_sim'
//|         if(t.rename_phase("start_of_sim",
//|               "renamed_start_of_sim") == 0)
//|            `vmm_error(log, " ... ");
//|         ...
//|      endfunction
//|   endclass 
function void vmm_timeline::prepend_callback(vmm_timeline_callbacks cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to prepend a NULL callback extension");
      return;
   end

   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Prepend new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback


// //////////////////////////////////////////// 
// Function: append_callback 
// 
// Appends the specified callback extension to the callback registry, for this timeline.
// Returns true, if the registration was successful. 
// 
//|   class timeline_callbacks extends vmm_timeline_callbacks;
//|      virtual function void my_f1();
//|      endfunction
//|   endclass
//|   
//|   class timelineExtension extends vmm_timeline;
//|      function new (string name, string inst, 
//|            vmm_unit parent=null);
//|         super.new(name,inst,parent);
//|      endfunction
//|   
//|      function void build_ph();
//|         `vmm_callback(timeline_callbacks,my_f1());
//|      endfunction:build_ph  
//|      ...
//|   endclass
//|   
//|   class timelineExtension_callbacks extends 
//|         timeline_callbacks;
//|      int my_f1_counter++;
//|      virtual function void my_f1();
//|         my_f1_counter++;
//|      endfunction
//|   endclass
//|   
//|   initial begin
//|      timelineExtension tl = new ("my_timeline", "t1");
//|      timelineExtension_callbacks cb1 = new();
//|      tl.append_callback(cb1);
//|      ...
//|   end
function void vmm_timeline::append_callback(vmm_timeline_callbacks cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to append a NULL callback extension");
      return;
   end

   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Append new callback
   this.callbacks.push_back(cb);
endfunction: append_callback


// //////////////////////////////////////////// 
// Function: unregister_callback 
// 
// Removes the specified callback extension from the callback registry, for this timeline.
// Returns true, if the unregistration was successful. 
// 
//|   class timeline_callbacks extends vmm_timeline_callbacks;
//|      virtual function void my_f1();
//|      endfunction
//|   endclass
//|   
//|   class timelineExtension extends vmm_timeline;
//|      function new (string name, string inst, vmm_unit 
//|            parent=null);
//|         super.new(name,inst,parent);
//|      endfunction
//|   
//|      function void build_ph();
//|         `vmm_callback(timeline_callbacks,my_f1());
//|      endfunction:build_ph  
//|      ...
//|   endclass
//|   
//|   class  timelineExtension_callbacks extends 
//|         timeline_callbacks;
//|      int my_f1_counter++;
//|      virtual function void my_f1();
//|         my_f1_counter++;
//|      endfunction
//|   endclass
//|   
//|   initial begin
//|      timelineExtension tl = new ("my_timeline", "t1");
//|      timelineExtension_callbacks cb1 = new();
//|      timelineExtension_callbacks cb2 = new();
//|      tl.append_callback(cb1);
//|      tl.append_callback(cb2);
//|      ...
//|      tl.unregister_callback(cb2);
//|      ...
//|   end
function void vmm_timeline::unregister_callback(vmm_timeline_callbacks cb);
   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         // Unregister it
         this.callbacks.delete(i);
         return;
      end
   end

   `vmm_warning(this.log, "Callback was not registered");
endfunction: unregister_callback

function bit vmm_timeline::is_stop_for_phase_set(string name);
   string phase_list = vmm_opts::get_string("break_on_phase" ,"", "specifies which phase to break on"); 
   string timeline_list = vmm_opts::get_string("break_on_timeline" ,"", "specifies which timeline to break on"); 
   if((timeline_list != "") && (timeline_list != break_on_timeline_last_seen)) begin
      string temp_str = "";
      break_on_timeline_last_seen = timeline_list;
      for (int index = 0; index < timeline_list.len(); index++) begin
        if (timeline_list[index] == "+") begin
          if (temp_str != "") 
            timeline_patterns.push_back(temp_str); 
          temp_str = "";
        end else begin
          temp_str = {temp_str,timeline_list[index]};
        end
      end
      if (temp_str != "")
        timeline_patterns.push_back(temp_str);
   end

   if (phase_list != "") begin
     if(phase_list != break_on_phase_last_seen) begin
        string temp_str = "";
        break_on_phase_last_seen = phase_list;
        for (int index = 0; index < phase_list.len(); index++) begin
          if (phase_list[index] == "+") begin
            if (temp_str != "")
              break_on_phase_hash[temp_str] = 1;
            temp_str = "";
          end else begin
            temp_str = {temp_str,phase_list[index]};
          end
        end
        if (temp_str != "")
          break_on_phase_hash[temp_str] = 1;
      end

     foreach (timeline_patterns[index]) begin
       vmm_object obj;
       vmm_object_iter iter = new(null,timeline_patterns[index]);
       obj = iter.first();
       if (obj == null) begin
         vmm_timeline tl;
         obj = find_object_by_name(timeline_patterns[index], "");
         if ((obj != null) && ($cast(tl, obj))) begin
           break_on_timeline_hash[tl.get_object_hiername()] = 1;
         end
       end else begin
         while (obj != null) begin
           vmm_timeline tl;
           if ($cast(tl, obj)) begin
             break_on_timeline_hash[tl.get_object_hiername()] = 1;
           end
           obj = iter.next();
         end
       end
     end
   end

   if (break_on_phase_hash[name] == 1) begin
      if (break_on_timeline_hash[get_object_hiername()] == 1) begin
         return 1;
      end else begin
         if (get_parent_object() == vmm_simulation::get_sim()) begin
            if (break_on_timeline_hash.num() != 0) begin
               return 0;
            end else begin
               return 1;
            end
        end else
          return 0;
      end
   end else
      return 0;
endfunction:is_stop_for_phase_set

// //////////////////////////////////////////// 
// Function: get_phase 
// 
// Returns the descriptor of the specified phase in this timeline. Returns null if the
// specified phase is unknown. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void build_ph();
//|         vmm_phase ph;
//|         vmm_timeline t = this.get_timeline();
//|         ...
//|         ph = t.get_phase ("start_of_sim"); 
//|         ...
//|      endfunction
//|   endclass 
function vmm_phase vmm_timeline::get_phase(string name);
   if (this.phase_impls.exists(name)) begin
      return this.phase_impls[name];
   end
   return null;
endfunction:get_phase

// //////////////////////////////////////////// 
// Function: get_current_phase_name 
// 
// Displays the current phase, where the timeline phase execution is at a given point of
// time. 
// 
//|   class test extends vmm_test;
//|      ...
//|      user_timeline topLevelTimeline;
//|      ... 
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      ...
//|      fork
//|         begin
//|            test1.topLevelTimeline.run_phase();    
//|         end
//|         begin
//|            #20 `vmm_note (log, psprintf("Current Simulation 
//|             Phase for test1 is : %s ", 
//|             test1.topLevelTimeline.get_current_phase_name()) 
//|           );
//|         end
//|         ...
//|      join
//|      ... 
//|   end 
function string vmm_timeline::get_current_phase_name();
   if(this.current_phase > -1)
      return this.phases[this.current_phase];
   else
      return "[No phase]";
endfunction:get_current_phase_name

// //////////////////////////////////////////// 
// Function: display_phases 
// 
// Displays all phases left to be executed, for this timeline. 
// 
//|   class test extends vmm_test;
//|      ...
//|      user_timeline topLevelTimeline;
//|      ... 
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      ...
//|      fork
//|         begin
//|            test1.topLevelTimeline.run_phase();    
//|         end
//|      begin
//|            #20 test1.topLevelTimeline.display_phases();
//|         end
//|         ...
//|      join
//|      ... 
//|   end
function void vmm_timeline::display_phases();
   if(this.phases.size !=0) begin
      foreach(this.phases[i]) begin
         if( (!this.phase_impls[phases[i]].is_phase_done())  && (i > this.current_phase))
            `vmm_note(this.log,`vmm_sformatf("Phase \"%s\" is pending for execution in this timeline ",this.phases[i]));
      end
   end
endfunction:display_phases

// //////////////////////////////////////////// 
// Function: get_previous_phase_name 
// 
// Returns the name of the phase that precedes the specified phase. Returns ^, if the specified
// phase is the first one. Returns ?, if the specified phase is unknown. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void build_ph ();
//|         string prv_ph; 
//|         vmm_timeline t = this.get_timeline();
//|         ...
//|         prv_ph = t.get_previous_phase_name ("start_of_sim"); 
//|            //returns "configure_test"
//|         ...
//|      endfunction
//|   endclass
function string vmm_timeline::get_previous_phase_name(string name);
   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         return (i == 0) ? "^" : this.phases[i-1];
      end
   end
   return "?";
endfunction:get_previous_phase_name

// //////////////////////////////////////////// 
// Function: get_next_phase_name 
// 
// Returns the name of the phase that follows the specified phase. Returns $, if the specified
// phase is the last one. Returns ?, if the specified phase is unknown. 
// 
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void build_ph ();
//|         string nxt_ph; 
//|         vmm_timeline t = this.get_timeline();
//|         ...
//|         nxt_ph = t.get_next_phase_name ("start_of_sim");
//|         //returns "reset"
//|         ...
//|      endfunction
//|   endclass  
function string vmm_timeline::get_next_phase_name(string name);
   if(name=="^" && this.phases.size()!=0) begin
      return this.phases[0];
   end
   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         return (i+1 == this.phases.size()) ? "$" : this.phases[i+1];
      end
   end
   return "?";
endfunction:get_next_phase_name

// //////////////////////////////////////////// 
// Function: step_function_phase 
// 
// Executes the specified function phase in this timeline. Must be a function phase, and
// must be the next executable phase. The fname and lineno arguments are used to track the
// file name and the line number where this method is invoked from. 
// 
//|   class test extends vmm_test;
//|      ...
//|      vmm_timeline topLevelTimeline;
//|      ... 
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      ...
//|      test1.topLevelTimeline.run_phase ("configure");
//|      test1.topLevelTimeline.step_function_phase ("connect");
//|      test1.topLevelTimeline.step_function_phase (
//|         "configure_test");
//|      ... 
//|   end
function void vmm_timeline::step_function_phase(string name, 
                                                string fname = "", 
												int lineno = 0);
   vmm_phase_impl impl;

   if (!this.phase_impls.exists(name)) 
      `vmm_warning_FL(this.log,`vmm_sformatf("Cannot schedule execution of unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
   else if (this.get_phase_method_type(name) == vmm_timeline::TASK) 
      `vmm_warning_FL(this.log,`vmm_sformatf("Cannot schedule execution of non-function phase %s for %s(%s) with step_function_phase",name,this.get_object_name(),this.get_typename()));
   else begin
      foreach(this.phases[i]) begin
         if(this.phases[i]==name) begin
            if(this.current_phase == i-1) begin
	       this.run_function_phase(name);
	    end
	 end
      end
   end
endfunction:step_function_phase

// //////////////////////////////////////////// 
// Function: abort_phase 
// 
// Aborts the execution of the specified phase, if it is the currently executing phase
// in the timeline. If another phase is executing, it generates a warning message if the
// specified phase is already executed to completion, and generates an error message
// if the specified phase is not yet started. The fname and lineno arguments are used to
// track the file name and the line number where this method is invoked from. 
// 
//|   class test extends vmm_test;
//|      vmm_timeline topLevelTimeline;
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      ...
//|      fork
//|         test1.topLevelTimeline.run_phase("reset");
//|         #(reset_cycle) test1.topLevelTimeline.abort_phase ( 
//|            "reset");
//|         ...
//|      join_any
//|      disable fork;
//|      ...
//|   end 
function void vmm_timeline::abort_phase(string name, 
                                        string fname = "", 
										int lineno = 0);
   foreach(this.phases[i]) begin
      if(this.phases[i]==name) begin
         if(this.current_phase > i) begin
            `vmm_warning_FL(this.log,`vmm_sformatf("Cannot abort phase %s for %s(%s) as is already executed",name,this.get_object_name(),this.get_typename()));
	    return;
	 end
         else if(this.current_phase < i) begin
            `vmm_error_FL(this.log,`vmm_sformatf("Cannot abort phase %s for %s(%s) when it hasn't even started execution",name,this.get_object_name(),this.get_typename()));
	    return;
	 end
         else begin
            `vmm_note_FL(this.log,`vmm_sformatf("abort set for phase %s ",name));
	    this.do_abort_phase = 1;
	 end
      end
   end
endfunction:abort_phase

function bit vmm_timeline::insert_phase_internal(string phase_name,
                                   string before_name,
                                   vmm_phase_def def,
                                   string fname = "",
				   int lineno = 0); 
   int idx = -1;


   if(def==null) begin
      `vmm_fatal_FL(this.log,`vmm_sformatf("%s(%s)::insert_phase() with NULL phase definition for phase %s is called",this.get_object_name(),this.get_typename(),phase_name));
      return 0;
   end 

   foreach (this.phases[i]) begin
       vmm_phase_impl impl = this.phase_impls[this.phases[i]];
       for (int j = 0; j < impl.defs.size(); j++) begin
           if (impl.defs[j] == def) begin
               `vmm_error_FL(this.log, 
                 `vmm_sformatf("Specified phase definition instance has already been used to define another Phase %s", 
                 this.phases[i]));
               return 0;
           end
       end
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == phase_name) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin         
            void'(log.text(
            `vmm_sformatf(
            "%s(%s)::insert_phase() for existing phase %s is called, hence adding new definition to existing one",
            this.get_object_name(),this.get_typename(),phase_name)));
            log.end_msg();
         end
         void'(this.add_phase(phase_name,def));
         return 1;
      end
   end

   if (before_name == "^") begin
      if (this.current_phase >= 0) begin
         idx = this.current_phase + 1;
         if (idx < this.phases.size()) begin
            this.phases.insert(idx, phase_name);
         end
         else this.phases.push_back(phase_name);
      end
      else begin
         this.phases.push_front(phase_name);
         idx = 0;
      end
   end

   if (before_name == "$") begin
      idx = this.phases.size();
      this.phases.push_back(phase_name);
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == before_name) begin
         idx = i;
         this.phases.insert(i, phase_name);
         break;
      end
   end

   if (idx < 0) begin
 	 `vmm_fatal_FL(this.log,`vmm_sformatf("Cannot insert phase before unknown phase for %s(%s)",this.get_object_name(),this.get_typename()));
   end

   if (this.current_phase >= idx) begin
 	 `vmm_fatal_FL(this.log,`vmm_sformatf("Cannot insert a new phase in the past %s(%s)",this.get_object_name(),this.get_typename()));
   end

   begin
      vmm_phase_impl impl = new(phase_name, this);
      this.phase_impls[phase_name] = impl;
      impl.defs.push_back(def);
   end
   
   return 1;
endfunction:insert_phase_internal

function bit vmm_timeline::add_phase(string name,
                          vmm_phase_def def);
   vmm_phase_impl impl;

   // Check if already defined, null, etc...
   if (!this.phase_impls.exists(name)) begin
 	 `vmm_fatal(this.log,`vmm_sformatf("Cannot add to unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
      return 0;
   end 

   impl = this.phase_impls[name];
   impl.defs.push_back(def);

   return 1;
endfunction:add_phase

// //////////////////////////////////////////// 
// Function: delete_phase 
// 
// Deletes the specified phase in this timeline. Returns false, if the phase does not exist.
// 
// The fname and lineno arguments are used to track the file name and the line number where
// this method is invoked from. 
// 
//|   class groupExtension extends vmm_group;
//|      function void build_ph ();
//|         vmm_timeline t = this.get_timeline();
//|         ...
//|         t.delete_phase ("connect");
//|         ...
//|      endfunction
//|   endclass
function bit vmm_timeline::delete_phase(string phase_name, 
                                        string fname = "",
										int lineno = 0);
   vmm_phase_impl impl;

   if (!this.phase_impls.exists(phase_name)) begin
 	 `vmm_warning_FL(this.log,`vmm_sformatf("Cannot delete unknown phase %s for %s(%s)",phase_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == phase_name) begin
         if (i <= this.current_phase) begin
 	       `vmm_warning_FL(this.log,`vmm_sformatf("Cannot delete a phase %s for %s(%s) after it has been executed ",phase_name,this.get_object_name(),this.get_typename()));
            return 0;
         end
         this.phases.delete(i);
         break;
      end
   end
   impl = this.phase_impls[phase_name];
   impl.kill_object();
   this.phase_impls.delete(phase_name);

   return 1;
endfunction:delete_phase

function bit vmm_timeline::rename_phase(string old_name, 
                                        string new_name, 
					 					string fname = "", 
										int lineno = 0);
   vmm_phase_impl impl;
   bit is_already_renamed;
   vmm_timeline tl = new("temp_timeline","tl");

   foreach(tl.phases[i]) begin
      if(old_name==tl.phases[i]) begin
         `vmm_warning_FL(this.log,`vmm_sformatf("Cannot rename default phase %s for %s(%s)",old_name,this.get_object_name(),this.get_typename()));
         return 0;
      end
   end
   tl = null;
   if (!this.phase_impls.exists(old_name)) begin
      `vmm_warning_FL(this.log,`vmm_sformatf("Cannot rename unknown phase %s for %s(%s)",old_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   if (this.phase_impls.exists(new_name)) begin
      `vmm_warning_FL(this.log,`vmm_sformatf("Phase with name \"%s\" already exists for %s(%s),hence ignoring rename_phase",old_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   /* cannot rename if executing or finished*/
   if(this.phase_impls[old_name].is_phase_done() || this.phase_impls[old_name].is_running()) begin
      `vmm_warning_FL(this.log,`vmm_sformatf("Cannot rename phase %s for %s(%s) while/after execution ",old_name,this.get_object_name(),this.get_typename()));
       return 0;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == old_name) begin
         this.phases[i] = new_name;
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
           void'(log.text(
           `vmm_sformatf(
           "Phase %s for %s(%s) has been renamed to %s ",old_name,
           this.get_object_name(),this.get_typename(),new_name)));
           log.end_msg();
         end
         break;
      end
   end

   impl = this.phase_impls[old_name];
   if(impl!=null) begin
      this.phase_impls[new_name] = impl;
      this.phase_impls[new_name].set_object_name(new_name);
      this.phase_impls.delete(old_name);
   end
   else
      return 0;

   return 1;
endfunction:rename_phase

// //////////////////////////////////////////// 
// Function: jump_to_phase 
// 
// Aborts the execution of the timeline, and immediately jumps to the beginning of the
// specified phase (but does not start executing it). Generates a warning message, if
// the specified phase is already started or completed. 
// Executing a phase without the intervening phases may cause severe damage to the state
// of the executing testcase and verification environment, and should be used with care.
// You should typically use to abort a testcase or simulation, and jump to the report phase.
// The fname and lineno arguments are used to track the file name and the line number where
// this method is invoked from. 
// 
//|   class timelineExtension #(string jump_phase = "report", 
//|         int delay_in_jump = 10) extends vmm_timeline;
//|      ...
//|      task reset_ph;
//|         #delay_in_jump jump_to_phase(jump_phase);
//|      endtask
//|      ...
//|   endclass
function void vmm_timeline::jump_to_phase(string name, 
                                          string fname = "", 
										  int lineno = 0);

   if (!this.phase_impls.exists(name)) begin
      `vmm_warning_FL(this.log,`vmm_sformatf("Cannot jump to unknown phase %s ",name));
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         if (i < this.current_phase) begin
 	    `vmm_warning_FL(this.log,`vmm_sformatf("Cannot jump to phase %s after it has been executed ",name));
	    return;
	 end
         if (i == this.current_phase) begin
 	    `vmm_warning_FL(this.log,`vmm_sformatf("Cannot jump to executing phase %s ",name));
	    return;
	 end
	 //abort executing phase ,set completion  flags for all jumped phases
 	    this.abort_phase(this.phases[this.current_phase]);

	 for(int j = this.current_phase+1; j < i;j++) begin
	    if(this.phase_impls.exists(this.phases[j])) begin
	       this.phase_impls[this.phases[j]].reset_running();
	       this.phase_executed[this.phases[j]]=1;
	       set_child_unit_executed(this.phases[j],this);
	       this.phase_impls[this.phases[j]].skipped_count ++ ;
	    end
	 end

         this.current_phase = i - 1;
	 //jump all subtimelines to specified phase
	 jump_child_to_phase(name,this);
      end
   end
 
endfunction:jump_to_phase

function void vmm_timeline::jump_child_to_phase(string name,
                                                vmm_object obj);
   vmm_object child;

   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      vmm_timeline tl;
      if ($cast(tl, child)) begin
         tl.jump_to_phase(name);
      end
      child = obj.get_nth_child(i++);
   end
endfunction:jump_child_to_phase

function void vmm_timeline::set_child_unit_executed(string name,
                                                    vmm_object obj);
   vmm_object child;

   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      vmm_unit un1;
      if ($cast(un1, child)) begin
         un1.phase_executed[name]=1;
      end
      child = obj.get_nth_child(i++);
   end
endfunction:set_child_unit_executed

// //////////////////////////////////////////// 
// 
// Task: run_phase 
// 
// Executes the phases in this timeline, up to and including the specified phase by argument
// name. For name $, run all phases. 
// The fname and lineno arguments are used to track the file name and the line number where
// this method is invoked from. 
// 
//|   class test extends vmm_test;
//|      ...
//|      vmm_timeline topLevelTimeline;
//|      ... 
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      test1.topLevelTimeline.run_phase ("build");
//|      ... 
//|      test1.topLevelTimeline.run_phase ();
//|   end
task vmm_timeline::run_phase(string name = "$", 
                             string fname = "",
                             int lineno = 0);
  
  if (!vmm_consensus::is_register_consensus()) begin
      vmm_simulation::register_unit_consensus();
  end
  if (this == vmm_simulation::get_pre_timeline())
    vmm_simulation::execute_pre_test(name);
  else 
    if(this == vmm_simulation::get_top_timeline()) begin
      vmm_simulation::execute_top_test(name);
    end
    else 
      if(this == vmm_simulation::get_post_timeline())
        vmm_simulation::execute_post_test(name);
      else 
        run_phase_internal(name, fname, lineno);


endtask : run_phase

task vmm_timeline::run_phase_internal(string name = "$", 
                                      string fname = "", 
						              int lineno = 0);
   int run_to = -1;
   string last_phase_to_run;
   last_phase_to_run = name;

   if (this.running != "") begin
 	 `vmm_fatal_FL(this.log,`vmm_sformatf("Timeline for %s(%s) already running to phase %s ",this.get_object_name(),this.get_typename(),this.running));
      return;
   end

   if (name == "$") run_to = this.phases.size() - 1;
   else begin
      foreach (this.phases[i]) begin
         if (this.phases[i] == name) begin
            run_to = i;
            break;
         end
      end
   end
   if (run_to < 0) begin
      // if the phase is unknown in this timeline, nothing to do!
      return;
   end

   this.running = name;
   
   while (this.current_phase < run_to) begin  // [[ while loop begins
     string name;
     int reset_ph_pos;
     vmm_phase_impl impl;

     this.current_phase++;

     if(this.phase_impls.exists(this.phases[this.current_phase])) begin
        if(this.phase_impls[this.phases[this.current_phase]].is_phase_done()) continue;
     end

     name = this.phases[this.current_phase];

     if(this.is_stop_for_phase_set(name)) begin
        if(callbacks.size() == 0)
	    $stop();
	else
           `vmm_callback(vmm_timeline_callbacks, break_on_phase(this,name));
     end

      // Bring all of the sub-timelines to the point where
      // they are ready to execute this phase
      if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
         void'(log.text( 
         `vmm_sformatf("get all children to phase  %s  in timeline  %s ...",
         name, this.get_object_name())));
         log.end_msg();
      end
      this.get_ready_for_phase(name, this);

      if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(log.text( 
            `vmm_sformatf("...Running phase  %s  in timeline  %s ...",
                          name, this.get_object_name())));
         log.end_msg();
      end
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.top_stream, name, "");
`endif

      impl = this.phase_impls[name];
      if (impl == null) begin
`ifdef VMM_TR_RECORD
         vmm_tr_record::end_tr(this.top_stream);
`endif
         continue;
      end

      this.phase_impls[name].set_running();
      fork // Limit the scope of wait fork
         begin
            automatic bit timeout_done,abort_done;
	    event running_phase_thread_done;
	    vmm_timeline tl;
 	    fork
 	       begin:running_phase_thread
                  `ifdef VMM_SV_SC_INTEROP // [[
                  fork
                     begin
                        this.run_phase_impl(name, impl);
                     end   
                     begin

                        // Sync VMM SC here in run_phase_internal.

                        if(is_sv2sc_interop == 1) begin

                            if (this.get_parent_object() == vmm_simulation::get_sim()) begin
                                  cont_execute_interop = 1;
                            end
                            else if(sync_sc_from_ph == name) begin
                                  cont_execute_interop = 1;
                            end;
                        
                            if(cont_execute_interop == 1) begin
                                vmm_sv2sc_sync_phase(name);
                            end
                        end
                     end   
                  join
                  `else
                     this.run_phase_impl(name, impl);
                  `endif // ]]
                  -> running_phase_thread_done;
 	       end
 	       begin:wait_for_timeout_thread
 	          delay_task(name,timeout_for_phases[name],running_phase_thread_done,timeout_done);
 	       end
 	       begin:check_for_abort_thread
 	          wait(this.do_abort_phase == 1 || running_phase_thread_done.triggered) ;
		     if(this.do_abort_phase == 1) begin
 		        abort_done = 1;
		     end
 	       end
	    join_any

 	    if(timeout_done==1) begin
`ifdef VMM_LOG_FORMAT_FILE_LINE 
               if (log.start_msg(vmm_log::FAILURE_TYP, errorsev_for_phases[name], fname, lineno)) begin 
`else 
               if (log.start_msg(vmm_log::FAILURE_TYP, errorsev_for_phases[name])) begin 
`endif 
	            void'(log.text(`vmm_sformatf("Timeout set for phase \"%s\" of timeline %s execution has expired",name,this.get_object_name()))); 
	            log.end_msg(); 
               end 
               this.phase_impls[name].timeout_done = 1;
	       set_timeout_done_for_child(name,this);
 	       disable fork;
 	    end
 	    else if(abort_done == 1) begin
 	       `vmm_warning_FL (this.log,`vmm_sformatf("Abort set for phase \"%s\" , hence aborting execution",name));
	       this.phase_impls[name].abort_done = 1;
	       this.phase_impls[name].abort_count ++ ;
	       set_abort_done_for_child(name,this);
 	       this.do_abort_phase = 0;
 	       disable fork;
	    end
         end
      join


`ifdef VMM_TR_RECORD
      vmm_tr_record::end_tr(this.top_stream);
`endif

	  //update ,if any phase deleted during recent executed phase
      if(last_phase_to_run == "$") run_to = this.phases.size() - 1;
      else begin
         foreach (this.phases[i]) begin
            if (this.phases[i] == last_phase_to_run) begin
               run_to = i ;
               break;
            end
         end
      end
   end  //  end of while loop ]]
   this.running = "";

   //if top timeline finished , flush all its subtimelines 
   begin
      vmm_timeline tl;
      bit flush_subtimelines;
      //check if root timeline and all phases are done including timeout & abort
      if(this.get_parent_object==null) begin
         this.set_run_subtimelines_to_end = 1;
         foreach(this.phase_impls[i]) begin
	    if(!this.phase_impls[i].is_phase_done()) begin
	       if(!this.phase_impls[i].abort_done || !this.phase_impls[i].timeout_done) begin
	          this.set_run_subtimelines_to_end = 0;
	       end
	    end
	 end
	 flush_subtimelines =   this.set_run_subtimelines_to_end;    
      end
      else if($cast(tl,this.get_root_object())) begin
	 flush_subtimelines =   tl.set_run_subtimelines_to_end;    
      end

      if(flush_subtimelines) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin  
            void'(log.text( 
            `vmm_sformatf( "All phases have been executed for top timeline (%s) , hence flushing all its subtimelines ",
            this.get_object_name())));
            log.end_msg();
         end
	 this.flush_child_timelines(this);
      end
   end

endtask:run_phase_internal

function void vmm_timeline::set_timeout_done_for_child(string name,
                                                       vmm_object obj);
   vmm_timeline tl;
   vmm_object   child;
   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
         `vmm_error (tl.log,`vmm_sformatf("Timeout set for phase \"%s\" of timeline %s execution has expired",name,tl.get_object_name()));
         tl.phase_impls[name].timeout_done = 1;
         tl.running = "";
      end
      child = obj.get_nth_child(i++);
   end
endfunction:set_timeout_done_for_child

task vmm_timeline::set_abort_done_for_child(string name,
                                            vmm_object obj);
   vmm_timeline tl;
   vmm_object   child;
   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
 	 `vmm_warning (tl.log,`vmm_sformatf("Abort set for phase \"%s\" , hence aborting execution",name));
	 tl.abort_child_phase_waiting(name,tl);
	 tl.phase_impls[name].abort_done = 1;
	 tl.phase_impls[name].abort_count ++ ;
         tl.running = "";
      end
      child = obj.get_nth_child(i++);
   end
   wait fork;
endtask:set_abort_done_for_child

task vmm_timeline::abort_child_phase_waiting(string name,
                                            vmm_object obj);
   vmm_unit   u1;
   vmm_object child;
   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(u1, child)) begin
         fork
	   wait(u1.phase_waiting[name]==0);
	 join_none
	 this.abort_child_phase_waiting(name,u1);
      end
      child = obj.get_nth_child(i++);
   end
   wait fork;
endtask:abort_child_phase_waiting

task vmm_timeline::flush_child_timelines(vmm_object obj);
         vmm_timeline tl2;
	 vmm_object   child;
	 int i = 0;
	 child = obj.get_nth_child(i++);
	 while (child != null) begin
	    if ($cast(tl2, child)) begin
               tl2.not_self_phased = 1;
	       tl2.run_phase("$");
	    end
	    child = obj.get_nth_child(i++);
	 end
endtask:flush_child_timelines

function void vmm_timeline::run_function_phase(string name);
   vmm_phase_impl impl;
   int unsigned def_count ;


   if (this.running != "") begin
      `vmm_fatal(this.log,`vmm_sformatf( "Timeline %s already running to phase %s",this.get_object_name(),this.running));
      return;
   end


   // Must be the next phase
   this.current_phase++;
   
   if (this.current_phase >= this.phases.size() ||
      (this.phases[this.current_phase] != name )) begin
      this.current_phase--;
      return;
   end

   if(this.is_stop_for_phase_set(name)) begin
      if(callbacks.size() == 0)
         $stop();
      else
         `vmm_callback(vmm_timeline_callbacks, break_on_phase(this,name));
   end

   if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(log.text(
      `vmm_sformatf("...Running phase  %s  in timeline  %s ...",name,this.get_object_name())));
      log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, name, "");
`endif

   impl = this.phase_impls[name];
   if (impl == null) return;

   foreach (impl.defs[i]) begin
      vmm_phase_def def = impl.defs[i];

      def_count ++;
      //check for any phase overiding definition
      if(this.override_phase_defs.exists(name)) begin
         def = this.override_phase_defs[name];
	     if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                void'(log.text( 
                `vmm_sformatf( "Using new definition of phase %s for %s(%s) ",
                name,this.get_object_name(),this.get_typename())));
             end
      end
      if (def.is_function_phase()) begin
         this.phase_impls[name].set_running();
         // If running on a top-level timeline, apply globally
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       vmm_timeline tl;
	       if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          if (!tl.phase_impls.exists(name)) continue ;
	       end
               def.run_function_phase(name,
                                      vmm_simulation::Xenv_rootsX[i],
                                      this.get_log());
	       if($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          if(tl.phase_impls.exists(name) && def_count == impl.defs.size()) begin
                     tl.phase_impls[name].reset_running();
		  end
	       end
            end
         end
         else begin
	    def.run_function_phase(name, this, this.get_log());
	    if(this.phase_impls.exists(name)) begin
               this.phase_impls[name].reset_running();
	    end
	 end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
            void'(log.text( 
            `vmm_sformatf("Phase %s is not a function...",name)));
            log.end_msg();
         end
         this.current_phase--;
         return;
      end
   end
endfunction:run_function_phase

// Bring all root and sub-timelines to the completion of the phase
// just before the specified phase
task vmm_timeline::get_ready_for_phase(string name,
                               vmm_object obj);
   vmm_timeline tl;
   vmm_group    gr;
   if (this.get_parent_object() == vmm_simulation::get_sim()) begin
      foreach (vmm_simulation::Xenv_rootsX[i]) begin
         if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
            vmm_phase ph = tl.get_phase(name);
            if (ph != null) begin
               ph = ph.previous_phase();
               if (ph != null) begin
	          if(!ph.is_phase_done()) begin
		     bit temp_bit;
		     temp_bit = tl.not_self_phased;
		     tl.not_self_phased = 0;
                     tl.run_phase(ph.get_object_name());
		     tl.not_self_phased = temp_bit;
		  end
	       end
	    end
            this.get_child_ready_for_phase(name,tl);
	 end else begin
           if ($cast(gr, vmm_simulation::Xenv_rootsX[i]))
             this.get_child_ready_for_phase(name, gr);
         end
      end
   end
   else this.get_child_ready_for_phase(name,obj);

endtask:get_ready_for_phase

task vmm_timeline::get_child_ready_for_phase(string name,
                                             vmm_object obj);
   vmm_timeline tl;
   vmm_object child;
   int i;


   i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
         vmm_phase ph = tl.get_phase(name);
         if (ph != null) begin
            ph = ph.previous_phase();
            if (ph != null) begin 
	       if(!ph.is_phase_done()) begin
		  bit temp_bit;
		  //don't set not_self_phased , as this phase will be run 
		  //for child before parent timeline execution starts 
		  //so it runs kind of self phased one
		  //tl.not_self_phased = 1;
		  temp_bit = tl.not_self_phased;
		  tl.not_self_phased = 0;
                  tl.run_phase(ph.get_object_name());
		  tl.not_self_phased = temp_bit;
	       end
	    end
	 end
      end
      else begin
	 this.get_child_ready_for_phase(name, child);
      end
      child = obj.get_nth_child(i++);
   end
endtask:get_child_ready_for_phase

// Hierarchically run phases in sub-units and sub-timelines
task vmm_timeline::run_phase_impl(string name,
                                  vmm_phase_impl impl);
   //vmm_timeline tl;
   int unsigned def_count;

   foreach (impl.defs[i]) begin
      vmm_timeline tl;
      vmm_phase_def def = impl.defs[i];

      def_count ++;
      //check for any phase overiding definition
      if(this.override_phase_defs.exists(name)) begin
         def = this.override_phase_defs[name];
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
            void'(log.text( 
            `vmm_sformatf( "Using new definition of phase %s for %s(%s) ",
            name,this.get_object_name(),this.get_typename())));
            log.end_msg();
         end
      end

      if (def.is_function_phase()) begin
         // If running on a top-level timeline, apply globally
         // except on unmarked vmm_test instances.
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          tl.get_ready_for_phase(name, tl);
                  tl.run_function_phase(name);
	       end
               else begin
	          this.get_ready_for_function_phase(name,vmm_simulation::Xenv_rootsX[i]);
	          def.run_function_phase(name,
                                      vmm_simulation::Xenv_rootsX[i],
                                      this.get_log());
	       end
	       if(this.phase_impls.exists(name) && def_count == impl.defs.size()) begin
                     this.phase_impls[name].reset_running();
	       end
            end
         end
         else  begin
	    def.run_function_phase(name, this, this.get_log());
	    if(this.phase_impls.exists(name) && def_count == impl.defs.size()) begin
               this.phase_impls[name].reset_running();
	    end
	 end
      end
      else begin
         bit last_impl_def;
         // If running on a top-level timeline, apply globally
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       def.run_task_phase(name,
                                  vmm_simulation::Xenv_rootsX[i],
                                  this.get_log());
            end
         end
         else begin
	    def.run_task_phase(name, this, this.get_log());
	 end
	 if(def_count == impl.defs.size()) last_impl_def = 1;
         this.wait_for_run_phase_impl_finish(name,last_impl_def);
      end
   end
endtask:run_phase_impl

task vmm_timeline::wait_for_run_phase_impl_finish(string name,
                                                  bit last_impl_def);
	 //should wait for top level objects execution to finish in case of vmm_simulation::run_test
	 //and particular timeline phase execution in case ran with run_phase
	 if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       vmm_unit u1;
	       if ($cast(u1,vmm_simulation::Xenv_rootsX[i])) begin
	          fork
		     begin
                        vmm_timeline tl = u1.get_timeline();
                        if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                           void'(log.text( 
                           `vmm_sformatf( "Waiting for root execution to finish for phase %s ",name)));
                           log.end_msg();
                        end
	                u1.phase_waiting[name]=1;
                        wait(u1.phase_executed[name]==1 );
	                u1.phase_waiting[name]=0;
                        if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                           void'(log.text( 
                           `vmm_sformatf( "Wait over for execution of phase %s ",name)));
                           log.end_msg();
                        end
			if($cast(tl,u1) && tl.phase_impls.exists(name))
			   tl.phase_impls[name].reset_running();
	                if(!last_impl_def) begin
                          u1.phase_executed[name]=0;
	                end
		     end
		  join_none
	       end
	    end
	    wait fork;
            this.phase_impls[name].reset_running();
	 end
	 else if(!this.not_self_phased) begin
	    this.phase_waiting[name]=1;
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text( 
               `vmm_sformatf( "Waiting for timeline execution to finish for phase %s ",name)));
               log.end_msg();
            end
            wait(this.phase_executed[name]==1 );
	    this.phase_waiting[name]=0;
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text( 
               `vmm_sformatf( "Wait over for execution of phase %s ",name)));
               log.end_msg();
            end
            this.phase_impls[name].reset_running();
	    if(!last_impl_def) begin
               this.phase_executed[name]=0;
	    end
	 end
	 else 
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text( 
               `vmm_sformatf( "Parent is waiting on this , no need to wait itself for phase %s ",name)));
               log.end_msg();
            end

endtask:wait_for_run_phase_impl_finish

task vmm_timeline::get_ready_for_function_phase(string name, 
                                                vmm_object obj);
   int i;
   vmm_timeline tl;
   vmm_object child;
   vmm_unit u1;
   i = 0;
   child = obj.get_nth_child(i++); 
   while (child != null) begin 
      if ($cast(tl, child))begin
         tl.not_self_phased = 1;
         tl.run_phase(name); 
      end
      else if($cast(u1,child)) begin
         vmm_timeline parent_tl;
	 parent_tl = u1.get_timeline();
         parent_tl.get_ready_for_function_phase(name,u1);
      end
      child = obj.get_nth_child(i++); 
   end
endtask:get_ready_for_function_phase

// //////////////////////////////////////////// 
// Function: reset_to_phase 
// 
// Resets this timeline to the specified phase name. Any task-based phase, which is concurrently
// running is aborted. If the timeline is reset to the configure phase or earlier, all of
// its vmm_unit sub-instances are enabled, along with itself. 
// The fname and lineno arguments are used to track the file name and the line number where
// this method is invoked from. 
// 
//|   class test extends vmm_test;
//|      user_timeline topLevelTimeline;
//|   endclass
//|   ...
//|   initial begin
//|      test test1 = new ("test1", "test1");
//|      fork
//|         test1.topLevelTimeline.run_phase();    
//|         //Assume topLevelTimeline is  going to run more 
//|         //than #9 delay
//|         #9 test1.topLevelTimeline.reset_to_phase ("build");
//|      join
//|   end
function void vmm_timeline::reset_to_phase(string name, 
                                           string fname = "", 
										   int lineno = 0);
   vmm_object child;
   vmm_timeline tl;
   int i ;
   int configure_ph_pos;

   foreach (this.phases[i]) begin
      if (this.phases[i] == "configure") 
         configure_ph_pos = i;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         if(i <= configure_ph_pos)  begin
            this.enable_child_unit(this,i);
         end
	 if(this.running!="") begin
 	    this.abort_phase(this.phases[this.current_phase]);
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text( 
               `vmm_sformatf("Aborting current executing phase \"%s\" for %s(%s) as reset_to_phase \"%s\" is executed",
               this.phases[this.current_phase],this.get_object_name(),this.get_typename(),name)));
               log.end_msg();
            end
	 end
         if (this.current_phase >= i) begin
            this.current_phase = i - 1;
         end
         break;
      end
   end

   this.reset_children_to_phase(name, this);

   // If a top-level timeline, apply globally
   if (this.get_parent_object() == vmm_simulation::get_sim()) begin
      foreach (vmm_simulation::Xenv_rootsX[i]) begin
         this.reset_children_to_phase(name, vmm_simulation::Xenv_rootsX[i]);
      end
      return;
   end
endfunction:reset_to_phase

function void vmm_timeline::reset_children_to_phase(string name, 
                                                    vmm_object obj);
   vmm_object child;
   vmm_timeline tl;
   vmm_unit   u1;

   int i = 0;
   int j = 0;

   /* reset all phase completion flags for phases greater than specified for timeline*/
   if($cast(tl,obj)) begin
      foreach(tl.phases[i]) begin
	 if(tl.phases[i]==name) begin
	   j = i;
           if (tl.current_phase >= i) begin
              tl.current_phase = i - 1;
           end
	 end
      end
      foreach(tl.phases[i]) begin
         if(i >= j) begin
	    if(tl.phase_impls.exists(tl.phases[i]))
               tl.phase_impls[tl.phases[i]].reset_done();
	    tl.phase_executed[tl.phases[i]] = 0;
	    tl.phase_impls[tl.phases[i]].abort_done = 0;
	 end
      end
   end
   /* reset all phase completion flags for unit phases corresponding to its timeline*/
   else if($cast(u1,obj)) begin
      vmm_timeline tl = u1.get_timeline();
      foreach(tl.phase_impls[i]) begin
         if(!tl.phase_impls[i].is_phase_done) begin
	    if(u1.phase_executed.exists(i))
	       u1.phase_executed[i] = 0;   
	 end
      end
   end
   
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) tl.reset_to_phase(name);
      else this.reset_children_to_phase(name, child);
      child = obj.get_nth_child(i++);
   end
endfunction:reset_children_to_phase

function void vmm_timeline::enable_child_unit(vmm_object obj,
                                              int unsigned ph_index);
   vmm_unit mod;
   vmm_object child;
   int i;

   i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(mod, child)) begin
         mod.enable_unit=1;
	 foreach(this.phases[j]) begin
	    if(j > ph_index && mod.phase_executed.exists(phases[j]))
	       mod.phase_executed[phases[j]] = 0;
	 end
         this.enable_child_unit(mod,ph_index);
      end
      else this.enable_child_unit(child,ph_index);
      child = obj.get_nth_child(i++);
   end
endfunction:enable_child_unit

// //////////////////////////////////////////// 
// Function: task_phase_timeout 
// 
// Sets the timeout value - as specified by delta - for the completion of the specified task
// phase. If the task phase does not complete within the time specified in the timeout value,
// then an error message is generated. Message severity, which is error by default, can
// be overridden using the error_severity argument.Returns false, if the specified
// phase does not exist or is not a task phase. 
// A timeout value of 0 specifies no timeout value. Calling this method, while the phase
// is currently executing, causes the timer to be reset to the specified value. By default,
// phases do not have timeouts. The fname and lineno arguments are used to track the file
// name and the line number where this method is invoked from. 
// 
//|   class groupExtension extends vmm_group;
//|      function void build_ph ();
//|         vmm_timeline t = this.get_timeline();
//|         if(t.task_phase_timeout("reset",4) == 0)
//|            `vmm_error (log, " ... ");
//|         ...
//|      endfunction
//|   endclass
function bit vmm_timeline::task_phase_timeout(string name, 
                                              int unsigned delta, 
                                              vmm_log::severities_e error_severity=vmm_log::ERROR_SEV,
					      					  string fname = "", 
										      int lineno = 0);
   if (!this.phase_impls.exists(name)) begin
 	 `vmm_warning_FL(this.log,`vmm_sformatf("Cannot set timeout for unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   /* if not task phase return FALSE */
   if(this.get_phase_method_type(name) != vmm_timeline::TASK) begin
 	 `vmm_warning_FL(this.log,`vmm_sformatf("Cannot set timeout for non-task phase %s of %s(%s)",name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   this.timeout_for_phases[name] = delta;
   this.errorsev_for_phases[name] = error_severity;
   return 1;
endfunction:task_phase_timeout

function vmm_timeline::METHOD_TYPE vmm_timeline::get_phase_method_type(string name);
   vmm_phase_impl impl;
   if (!this.phase_impls.exists(name)) begin
 	 `vmm_fatal(this.log,`vmm_sformatf("Cannot find method type for unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
      return vmm_timeline::INVALID_TYPE;
   end

   impl = this.phase_impls[name];
   if (impl == null) return vmm_timeline::INVALID_TYPE;

   foreach (impl.defs[i]) begin
      if (impl.defs[i].is_task_phase()) begin
 	 return vmm_timeline::TASK;
	 break;
      end
      else if (impl.defs[i].is_function_phase()) begin
 	 return vmm_timeline::FUNCTION;
	 break;
      end
   end
endfunction:get_phase_method_type

// //////////////////////////////////////////// 
// Function: insert_phase 
// 
// Creates the specified phase (phase_name) before the specified phase (before_name)
// in this timeline, and issues a note that a new user-defined phase is defined. The argument
// def specifies the phase instance to be inserted. If the phase already exists, adds this
// definition to the existing phase definition. If the before_name is specified as a caret
// (^), then inserts the phase at the beginning of the timeline. If it is specified as a dollar
// sign ($), then inserts the phase at the end of the timeline. Returns true, if the phase
// insertion was successful. 
// The fname and lineno arguments are used to track the file name and the line number where
// this method is invoked from. 
// 
//|   class udf_start_def extends vmm_fork_task_phase_def   
//|         #(groupExtension);
//|      ...
//|   endclass
//|   class groupExtension extends vmm_group;
//|      ...
//|      function void build_ph ();
//|         vmm_timeline t = this.get_timeline();
//|         udf_start_def udfstartph = new;
//|         ...
//|         if(t.insert_phase("udf_start", "start_of_sim",
//|               udfstartph) == 0)
//|            `vmm_error (log, " ... ");
//|      endfunction
//|   endclass
function bit vmm_timeline::insert_phase(string phase_name,
                   		                string before_name,
                        		        vmm_phase_def def,
					  				    string fname = "",
									    int lineno = 0);
   int idx,before_name_ph_idx;

   //User warning , that no task phase should be inserted before start_of_sim phase
   //TBD 
   /*
   if(def.is_task_phase==1) begin
     idx = get_phase_index("start_of_sim");
     before_name_ph_idx = get_phase_index(before_name);
     if(before_name_ph_idx <= idx) begin
        `vmm_warning(this.log,`vmm_sformatf("Task phase %s should't be inserted before start_of_sim phase",phase_name));
     end
   end
   //TBD check that before name specified can't be in the running state
*/
   if ((this.get_parent_object() == vmm_simulation::get_sim()) &&  (vmm_simulation::is_allowed_new_phases() == 0) ) begin
      `vmm_error_FL(this.log, "Insertion of user-defined phases in pre/top/post timelines is disabled by default\nTo enable please use vmm_simulation::allow_new_phases(1)");
       return(0);
   end

   if(this.insert_phase_internal(phase_name,before_name,def)) begin
      `vmm_note_FL(this.log,`vmm_sformatf("%s(%s)::insert_phase() inserted phase %s before phase %s",this.get_object_name(),this.get_typename(),phase_name,before_name));
      return 1;
   end
   else
      return 0;
endfunction:insert_phase

task vmm_timeline::delay_task(string name,
                              int unsigned delay,
                              event running_phase_thread_done,
                              output bit timeout_done);
 int new_delay = -1;
 bit running_phase_done = 0;
fork begin
 fork
    begin
       if(delay!=0) begin
          # delay;
       end
       else begin
	  @(timeout_for_phases[name]);
	  new_delay = timeout_for_phases[name];
       end
    end
    begin
       if(this.timeout_for_phases.exists(name) && this.timeout_for_phases[name]!= delay) begin
	  new_delay = timeout_for_phases[name];
       end
       else begin
          @(timeout_for_phases[name]);
	  new_delay = timeout_for_phases[name];
       end
    end
    begin
       wait(running_phase_thread_done.triggered);
       running_phase_done = 1;
    end
 join_any
 disable fork;
end
join
 if(new_delay!= -1 && running_phase_done!=1) begin
       delay_task(name,this.timeout_for_phases[name],running_phase_thread_done, timeout_done);
 end else 
  if(new_delay == -1 && running_phase_done != 1)
    timeout_done = 1;
endtask:delay_task

task vmm_timeline::phase_wait_finish(string name, 
                                     vmm_object obj);
   vmm_unit u1;
   $cast(u1,obj);
   fork begin
   fork
      this.wait_for_child_phase_finish(name,u1);
      wait(this.do_abort_phase == 1);
   join_any
   disable fork;
  end
join
endtask:phase_wait_finish

task vmm_timeline::wait_for_child_phase_finish(string name, 
                                                     vmm_object obj);
   vmm_timeline tl1;
   vmm_unit     u1;
   vmm_object   child;
   vmm_subenv   subenv;
   int i = 0;

  if(!$cast(subenv, obj)) begin
  // wait for completion of all unit type children of this timeline 
     child = obj.get_nth_child(i++);
     while (child != null) begin
        this.wait_object_to_finish_phase(name,child);
        child = obj.get_nth_child(i++);
     end
   end
 wait fork;

endtask:wait_for_child_phase_finish


task vmm_timeline::wait_object_to_finish_phase(string name, 
                                                     vmm_object obj);
   vmm_timeline tl;
   vmm_unit     u1;
   int i = 0;

   if ( $cast(u1, obj)) 
      if(!u1.is_implicitly_phased()) return; 
    //don't wait for phase completion for timelines 
      //2) whose timeline doesn't have this particular phase (deleted etc.) 
	  
   // wait for completion of timeline's own phase 
   if (obj!= null && $cast(tl, obj)) begin
      bit dont_wait = (!tl.phase_impls.exists(name)) ; 
      if (!dont_wait ) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
            void'(log.text(
            `vmm_sformatf( "Waiting for execution to finish for phase %s ",name)));
            log.end_msg();
         end
	 fork 
	    begin
	       tl.phase_waiting[name]=1;
               wait(tl.phase_executed[name]==1 || tl.do_abort_phase == 1 );
               tl.phase_impls[name].reset_running();
	       if(tl.do_abort_phase == 1)begin
	          tl.phase_waiting[name]=0;
	       end
	       else
                  if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                     void'(log.text( 
                     `vmm_sformatf( "Wait over for execution of phase %s ",name)));
                     log.end_msg();
                  end
	    end
	 join_none
      end
   end
   
   // wait for completion of  units 
   if ( (!$cast(tl,obj)) && $cast(u1, obj)) begin
      //don't wait for phase completion for units 
      //which is disabled and reset phase is executed 
      
      bit dont_wait = (!u1.is_unit_enabled() && u1.phase_executed["reset"]) ; 
      if(!dont_wait ) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
            void'(log.text( 
            `vmm_sformatf( "Waiting for execution to finish for phase %s ",name)));
            log.end_msg();
         end
	 fork   
	    begin
               vmm_timeline tl1 = u1.get_timeline();
	       u1.phase_waiting[name]=1;
               wait(u1.phase_executed[name]==1 || tl1.do_abort_phase == 1);
	       if(tl1.do_abort_phase == 1) begin
	          u1.phase_waiting[name]=0;
	       end
	       else
                  if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                     void'(log.text(
                     `vmm_sformatf( "Wait over for execution of phase %s ",name)));
                     log.end_msg();
                  end
	    end
	 join_none
      end
   end
endtask:wait_object_to_finish_phase

function void vmm_timeline::update_for_current_phase_counter(string name);
   bit set_current_phase;
   int new_current_phase;
   foreach (this.phases[i]) begin
      if(this.phases[i] == name) begin
         set_current_phase = (this.phases[this.current_phase] != name ) &&
	                         ( this.current_phase < i);
         new_current_phase = i;
         break;
      end
   end
   if(set_current_phase) begin
      this.current_phase = new_current_phase;
   end
endfunction


function void vmm_timeline::display_phase_info();
   string phases_done[$];
   string phases_tbd[$];
   string current_ph;
   int width = 5;
   string my_str;
   bit all_done = 0;
   string _temp = " ";
   if(this.phases.size !=0) begin
      foreach(this.phases[i]) begin
         if (this.phases[i].len() > width) width = this.phases[i].len();
         if ( (this.phase_impls[phases[i]].is_phase_done())) begin
            if  ( i < this.current_phase)
               phases_done.push_back(this.phases[i]);
            else begin
               if (i+1 != this.phases.size()) current_ph = this.phases[i];
               else begin
                  phases_done.push_back(this.phases[i]);
                  all_done = 1;
               end
            end
         end
         if( (!this.phase_impls[phases[i]].is_phase_done())) begin
             if (i > this.current_phase)
                phases_tbd.push_back(this.phases[i]);
             else
                current_ph = this.phases[i];
         end
      end
      width = width+5;
      if (phases_done.size !=0) begin
         foreach(phases_done[i]) begin
            $display("\t%s%s : Done",phases_done[i],{width - phases_done[i].len() {_temp}});
         end
      end
      if (current_ph == "") begin
         if (all_done == 0)
            $display("\tphase execution not yet started");
      end
      else begin
         if (current_ph.len() < width)
            $display("\t%s%s : Executing..............",current_ph,{width - current_ph.len {" "}});
      end
      if(phases_tbd.size !=0) begin
         foreach(phases_tbd[i]) begin
            $display("\t%s%s : Pending",phases_tbd[i],{width - phases_tbd[i].len() {" "}});
         end
      end
   end
endfunction:display_phase_info

`ifdef VMM_SV_SC_INTEROP

function void vmm_timeline::sync_sv2sc_interop();
  sync_sc_from_ph = "configure_test";
endfunction:sync_sv2sc_interop

function void vmm_timeline::set_sv2sc_interop();
  if(is_sc2sv_interop == 0) 
      is_sv2sc_interop = 1;
  else
    `vmm_error(this.log,"Direction is already set to SC2SV for interop mode");
endfunction:set_sv2sc_interop

function void vmm_timeline::set_sc2sv_interop();
  if(is_sv2sc_interop == 0) 
     is_sc2sv_interop = 1;
  else
    `vmm_error(this.log,"Direction is already set to SV2SC for interop mode");
endfunction:set_sc2sv_interop

`endif
