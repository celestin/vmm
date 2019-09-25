/*********************************************************************
 *    Copyright 2004-2009 Synopsys, Inc.
 *    All Rights Reserved Worldwide
 *
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

function vmm_phase::new(string name, 
                        vmm_timeline parent);
   super.new(parent, name);
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

function vmm_timeline::new(string name = "", 
                           string inst = "",
			   vmm_object parent);
   super.new(name,inst, parent);

   // Pre-defined run-time phases
   begin
      vmm_rtl_config_phase_def       rtl_config_ph = new;
      vmm_unit_buildph_phase_def     build_ph      = new;
      vmm_unit_configph_phase_def    config_ph     = new;
      vmm_unit_connectph_phase_def   connect_ph    = new;
      vmm_unit_startsimph_phase_def  startsim_ph   = new;
      vmm_unit_resetph_phase_def     reset_ph      = new;
      vmm_unit_trainingph_phase_def  training_ph   = new;
      vmm_unit_configdut_phase_def   configdut_ph  = new;
      vmm_unit_startph_phase_def     start_ph      = new; 
      vmm_unit_starttestph_phase_def starttest_ph  = new;
      vmm_unit_run_testph_phase_def  run_test_ph   = new;
      vmm_unit_shutdownph_phase_def  shutdown_ph   = new;
      vmm_unit_cleanupph_phase_def   cleanup_ph    = new;
      vmm_unit_reportph_phase_def    report_ph     = new;
      vmm_unit_destructph_phase_def  destruct_ph   = new;


      this.insert_phase_internal("rtl_config",   "$", rtl_config_ph);
      this.insert_phase_internal("build",        "$", build_ph);
      this.insert_phase_internal("configure",    "$", config_ph);
      this.insert_phase_internal("connect",      "$", connect_ph);
      this.insert_phase_internal("start_of_sim", "$", startsim_ph);
      this.insert_phase_internal("reset",        "$", reset_ph);
      this.insert_phase_internal("training",     "$", training_ph);
      this.insert_phase_internal("config_dut",   "$", configdut_ph);
      this.insert_phase_internal("start",        "$", start_ph);
      this.insert_phase_internal("start_of_test","$", starttest_ph);
      this.insert_phase_internal("run_test",     "$", run_test_ph);
      this.insert_phase_internal("shutdown",     "$", shutdown_ph);
      this.insert_phase_internal("cleanup",      "$", cleanup_ph);
      this.insert_phase_internal("report",       "$", report_ph);
      this.insert_phase_internal("destruct",     "$", destruct_ph);
   end
endfunction:new

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
   string run_time_option;
   run_time_option = {"break_on_",name,"_phase"};
   void'(vmm_opts::get_object_bit(is_stop_for_phase_set,this,run_time_option,"",0)); 
   return(is_stop_for_phase_set);
endfunction:is_stop_for_phase_set

function vmm_phase vmm_timeline::get_phase(string name);
   if (this.phase_impls.exists(name)) begin
      return this.phase_impls[name];
   end
   return null;
endfunction:get_phase

function string vmm_timeline::get_current_phase_name();
   if(this.current_phase >= -1)
      return this.phases[this.current_phase];
   else
      return "[No phase]";
endfunction:get_current_phase_name

function void vmm_timeline::display_phases();
   if(this.phases.size !=0) begin
      foreach(this.phases[i]) begin
         if( (!this.phase_impls[phases[i]].is_phase_done())  && (i > this.current_phase))
            `vmm_note(this.log,`vmm_sformatf("Phase \"%s\" is pending for execution in this timeline ",this.phases[i]));
      end
   end
endfunction:display_phases

function string vmm_timeline::get_previous_phase_name(string name);
   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         return (i == 0) ? "^" : this.phases[i-1];
      end
   end
   return "?";
endfunction:get_previous_phase_name

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

function void vmm_timeline::step_function_phase(string name, 
                                                string fname, 
						int lineno);
   vmm_phase_impl impl;

   if (!this.phase_impls.exists(name)) 
      `vmm_warning(this.log,`vmm_sformatf("Cannot schedule execution of unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
   else if (this.get_phase_method_type(name) == vmm_timeline::TASK) 
      `vmm_warning(this.log,`vmm_sformatf("Cannot schedule execution of non-function phase %s for %s(%s) with step_function_phase",name,this.get_object_name(),this.get_typename()));
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

function void vmm_timeline::abort_phase(string name, 
                                        string fname, 
					int lineno);
   foreach(this.phases[i]) begin
      if(this.phases[i]==name) begin
         if(this.current_phase > i) begin
            `vmm_warning(this.log,`vmm_sformatf("Cannot abort phase %s for %s(%s) as is already executed",name,this.get_object_name(),this.get_typename()));
	    return;
	 end
         else if(this.current_phase < i) begin
            `vmm_error(this.log,`vmm_sformatf("Cannot abort phase %s for %s(%s) when it hasn't even started execution",name,this.get_object_name(),this.get_typename()));
	    return;
	 end
         else this.do_abort_phase = 1;
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
      `vmm_fatal(this.log,`vmm_sformatf("%s(%s)::insert_phase() with NULL phase definition for phase %s is called",this.get_object_name(),this.get_typename(),phase_name));
      return 0;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == phase_name) begin
         `vmm_debug(this.log,`vmm_sformatf("%s(%s)::insert_phase() for existing phase %s is called, hence adding new definition to existing one",this.get_object_name(),this.get_typename(),phase_name));
         this.add_phase(phase_name,def);
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
 	 `vmm_fatal(this.log,`vmm_sformatf("Cannot insert phase before unknown phase for %s(%s)",this.get_object_name(),this.get_typename()));
   end

   if (this.current_phase >= idx) begin
 	 `vmm_fatal(this.log,`vmm_sformatf("Cannot insert a new phase in the past %s(%s)",this.get_object_name(),this.get_typename()));
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

function bit vmm_timeline::delete_phase(string phase_name, 
                                        string fname,
					int lineno);
   vmm_phase_impl impl;

   if (!this.phase_impls.exists(phase_name)) begin
 	 `vmm_warning(this.log,`vmm_sformatf("Cannot delete unknown phase %s for %s(%s)",phase_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == phase_name) begin
         if (i <= this.current_phase) begin
 	       `vmm_warning(this.log,`vmm_sformatf("Cannot delete a phase %s for %s(%s) after it has been executed ",phase_name,this.get_object_name(),this.get_typename()));
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
					 string fname, 
					 int lineno);
   vmm_phase_impl impl;
   bit is_already_renamed;
   vmm_timeline tl = new("temp_timeline","tl");

   foreach(tl.phases[i]) begin
      if(old_name==tl.phases[i]) begin
         `vmm_warning(this.log,`vmm_sformatf("Cannot rename default phase %s for %s(%s)",old_name,this.get_object_name(),this.get_typename()));
         return 0;
      end
   end
   tl = null;
   if (!this.phase_impls.exists(old_name)) begin
      `vmm_warning(this.log,`vmm_sformatf("Cannot rename unknown phase %s for %s(%s)",old_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   if (this.phase_impls.exists(new_name)) begin
      `vmm_warning(this.log,`vmm_sformatf("Phase with name \"%s\" already exists for %s(%s),hence ignoring rename_phase",old_name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   /* cannot rename if executing or finished*/
   if(this.phase_impls[old_name].is_phase_done() || this.phase_impls[old_name].is_running()) begin
      `vmm_warning(this.log,`vmm_sformatf("Cannot rename phase %s for %s(%s) while/after execution ",old_name,this.get_object_name(),this.get_typename()));
       return 0;
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == old_name) begin
         this.phases[i] = new_name;
         `vmm_debug(this.log,`vmm_sformatf("Phase %s for %s(%s) has been renamed to %s ",old_name,this.get_object_name(),this.get_typename(),new_name));
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

function void vmm_timeline::jump_to_phase(string name, 
                                          string fname, 
					  int lineno);

   if (!this.phase_impls.exists(name)) begin
      `vmm_warning(this.log,`vmm_sformatf("Cannot jump to unknown phase %s ",name));
   end

   foreach (this.phases[i]) begin
      if (this.phases[i] == name) begin
         if (i < this.current_phase) begin
 	    `vmm_warning(this.log,`vmm_sformatf("Cannot jump to phase %s after it has been executed ",name));
	    return;
	 end
         if (i == this.current_phase) begin
 	    `vmm_warning(this.log,`vmm_sformatf("Cannot jump to executing phase %s ",name));
	    return;
	 end
	 //abort executing phase ,set completion  flags for all jumped phases
	 if(this.running!="") begin
 	    this.abort_phase(this.phases[this.current_phase]);
	 end

	 for(int j = this.current_phase+1; j < i;j++) begin
	    if(this.phase_impls.exists(this.phases[j])) begin
	       this.phase_impls[this.phases[j]].reset_running();
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

task vmm_timeline::run_phase(string name, 
                             string fname, 
			     int lineno);
   int run_to = -1;
   string last_phase_to_run;

   last_phase_to_run = name;

   if (this.running != "") begin
 	 `vmm_fatal(this.log,`vmm_sformatf("Timeline for %s(%s) already running to phase %s ",this.get_object_name(),this.get_typename(),this.running));
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

   while (this.current_phase < run_to) begin
     string name;
     int reset_ph_pos;
     vmm_phase_impl impl;

     this.current_phase++;

     if(this.phase_impls.exists(this.phases[this.current_phase])) begin
        if(this.phase_impls[this.phases[this.current_phase]].is_phase_done()) continue;
     end

     name = this.phases[this.current_phase];

     if(this.is_stop_for_phase_set(name)) begin
        if(callbacks.empty())
	    $stop();
	else
           `vmm_callback(vmm_timeline_callbacks, break_on_phase(this,name));
     end

      // Bring all of the sub-timelines to the point where
      // they are ready to execute this phase
      this.get_ready_for_phase(name, this);

      `vmm_trace(this.log,`vmm_sformatf("...Running phase  %s  in timeline  %s ...",name,this.get_object_name()));


      impl = this.phase_impls[name];
      if (impl == null) continue;

      this.phase_impls[name].set_running();
      fork // Limit the scope of wait fork
         begin
            automatic bit timeout_done,abort_done;
	    automatic bit running_phase_thread_done;
	    vmm_timeline tl;
 	    fork
 	       begin:running_phase_thread
                  this.run_phase_impl(name, impl);
                  if(this.get_phase_method_type(name) == vmm_timeline::TASK) begin
                     if (this.get_parent_object() == vmm_simulation::get_sim()) begin
                        foreach (vmm_simulation::Xenv_rootsX[i]) begin
			   if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
			      if (!tl.phase_impls.exists(name)) continue ;
		              else if(tl.phase_impls.exists(tl.get_previous_phase_name(name)))
		                      if(!tl.phase_impls[tl.get_previous_phase_name(name)].is_phase_done()) continue;
			   end
		           this.wait_child_object_to_finish_phase(name,vmm_simulation::Xenv_rootsX[i]);
			   if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) 
                              tl.phase_impls[name].reset_running();
		        end
		     end
		     else begin
		        this.wait_child_object_to_finish_phase(name,this);
                        this.phase_impls[name].reset_running();
		     end
		  end
		  running_phase_thread_done = 1;
 	       end
 	       begin:wait_for_timeout_thread
 	          delay_task(name,timeout_for_phases[name],running_phase_thread_done);
		  if(running_phase_thread_done!=1)
 		     timeout_done =1;
 	       end
 	       begin:check_for_abort_thread
 	          wait(this.do_abort_phase == 1 || running_phase_thread_done == 1) ;
		     if(running_phase_thread_done != 1) begin
 		        abort_done = 1;
 		        this.do_abort_phase = 0;
		     end
 	       end
	    join_any

 	    if(timeout_done==1) begin
 	       `vmm_error (this.log,`vmm_sformatf("Timeout set for phase \"%s\" of timeline %s execution has expired",name,this.get_object_name()));
               this.phase_impls[name].timeout_done = 1;
	       set_timeout_done_for_child(name,this);
 	       disable fork;
 	    end
 	    else if(abort_done == 1) begin
 	       `vmm_warning (this.log,`vmm_sformatf("Abort set for phase \"%s\" , hence aborting execution",name));
	       this.phase_impls[name].abort_done = 1;
	       this.phase_impls[name].abort_count ++ ;
	       set_abort_done_for_child(name,this);
 	       disable fork;
	    end
         end
      join

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
   end
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
	 `vmm_debug(this.log,`vmm_sformatf( "All phases have been executed for top timeline (%s) , hence flushing all its subtimelines ",this.get_object_name()));
	 this.flush_child_timelines(this);
      end
   end

endtask:run_phase

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

function void vmm_timeline::set_abort_done_for_child(string name,
                                                     vmm_object obj);
   vmm_timeline tl;
   vmm_object   child;
   int i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
 	 `vmm_warning (tl.log,`vmm_sformatf("Abort set for phase \"%s\" , hence aborting execution",name));
	 tl.phase_impls[name].abort_done = 1;
	 tl.phase_impls[name].abort_count ++ ;
         tl.running = "";
      end
      child = obj.get_nth_child(i++);
   end
endfunction:set_abort_done_for_child

task vmm_timeline::flush_child_timelines(vmm_object obj);
         vmm_timeline tl2;
	 vmm_object   child;
	 int i = 0;
	 child = obj.get_nth_child(i++);
	 while (child != null) begin
	    if ($cast(tl2, child)) begin
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
      if(callbacks.empty())
         $stop();
      else
         `vmm_callback(vmm_timeline_callbacks, break_on_phase(this,name));
   end

   `vmm_trace(this.log,`vmm_sformatf("...Running phase  %s  in timeline  %s ...",name,this.get_object_name()));

   impl = this.phase_impls[name];
   if (impl == null) return;

   foreach (impl.defs[i]) begin
      vmm_phase_def def = impl.defs[i];

      def_count ++;
      //check for any phase overiding definition
      if(this.override_phase_defs.exists(name)) begin
         def = this.override_phase_defs[name];
	     `vmm_debug(this.log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,this.get_object_name(),this.get_typename()));
      end
      if (def.is_function_phase()) begin
         this.phase_impls[name].set_running();
         // If running on a top-level timeline, apply globally
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       vmm_timeline tl;
	       if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          if (!tl.phase_impls.exists(name)) continue ;
		  else if(tl.phase_impls.exists(tl.get_previous_phase_name(name)))
		          if(!tl.phase_impls[tl.get_previous_phase_name(name)].is_phase_done()) continue;
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
 	 `vmm_debug(this.log,`vmm_sformatf("Phase %s is not a function...",name));
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
   if (this.get_parent_object() == vmm_simulation::get_sim()) begin
      foreach (vmm_simulation::Xenv_rootsX[i]) begin
         if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
            vmm_phase ph = tl.get_phase(name);
            if (ph != null) begin
               ph = ph.previous_phase();
               if (ph != null) begin
	          if(!ph.is_phase_done()) 
                     tl.run_phase(ph.get_object_name());
	       end
	    end
            this.get_child_ready_for_phase(name,tl);
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
	       if(!ph.is_phase_done())
                  tl.run_phase(ph.get_object_name());
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
 	 `vmm_debug(this.log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,this.get_object_name(),this.get_typename()));
      end

      if (def.is_function_phase()) begin
         // If running on a top-level timeline, apply globally
         // except on unmarked vmm_test instances.
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          bit foreach_continue = !tl.phase_impls.exists(name) ||
		                         ((tl.phase_impls.exists(tl.get_previous_phase_name(name)))  
					      && (!tl.phase_impls[tl.get_previous_phase_name(name)].is_phase_done()));
	          if (foreach_continue) continue ;
                  tl.run_function_phase(name);
	       end
               else def.run_function_phase(name,
                                      vmm_simulation::Xenv_rootsX[i],
                                      this.get_log());
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
         // If running on a top-level timeline, apply globally
         if (this.get_parent_object() == vmm_simulation::get_sim()) begin
            foreach (vmm_simulation::Xenv_rootsX[i]) begin
	       if ($cast(tl,vmm_simulation::Xenv_rootsX[i])) begin
	          bit foreach_continue = !tl.phase_impls.exists(name) ||
		                         ((tl.phase_impls.exists(tl.get_previous_phase_name(name)))  
					      && (!tl.phase_impls[tl.get_previous_phase_name(name)].is_phase_done()));
	          if (foreach_continue) continue ;
	       end
               def.run_task_phase(name,
                                  vmm_simulation::Xenv_rootsX[i],
                                  this.get_log());
            end
         end
         else begin
	    def.run_task_phase(name, this, this.get_log());
	 end
      end
   end
endtask:run_phase_impl

function void vmm_timeline::reset_to_phase(string name, 
                                           string fname, 
					   int lineno);
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
            `vmm_debug(this.log,`vmm_sformatf("Aborting current executing phase \"%s\" for %s(%s) as reset_to_phase \"%s\" is executed",this.phases[this.current_phase],this.get_object_name(),this.get_typename(),name));
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
	 end
      end
      foreach(tl.phases[i]) begin
         if(i >= j) begin
	    if(tl.phase_impls.exists(tl.phases[i]))
               tl.phase_impls[tl.phases[i]].reset_done();
	    tl.phase_executed[tl.phases[i]] = 0;
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

function bit vmm_timeline::task_phase_timeout(string name, 
                                              int unsigned delta, 
					      string fname, 
					      int lineno);
   if (!this.phase_impls.exists(name)) begin
 	 `vmm_warning(this.log,`vmm_sformatf("Cannot set timeout for unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   /* if not task phase return FALSE */
   if(this.get_phase_method_type(name) != vmm_timeline::TASK) begin
 	 `vmm_warning(this.log,`vmm_sformatf("Cannot set timeout for non-task phase %s of %s(%s)",name,this.get_object_name(),this.get_typename()));
      return 0;
   end

   this.timeout_for_phases[name] = delta;
   return 1;
endfunction:task_phase_timeout

function vmm_timeline::METHOD_TYPE vmm_timeline::get_phase_method_type(string name);
   vmm_phase_impl impl;
   if (!this.phase_impls.exists(name)) begin
 	 `vmm_fatal(this.log,`vmm_sformatf("Cannot find method type for unknown phase %s for %s(%s)",name,this.get_object_name(),this.get_typename()));
      return "";
   end

   impl = this.phase_impls[name];
   if (impl == null) return "";

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

function bit vmm_timeline::insert_phase(string phase_name,
                                   string before_name,
                                   vmm_phase_def def,
				   string fname,
				   int lineno);
   int idx,before_name_ph_idx;

   //User warning , that no task phase should be inserted before start_of_sim phase
   //TBD if start_of_sim name changed then ?
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
   if(this.insert_phase_internal(phase_name,before_name,def)) begin
      `vmm_note(this.log,`vmm_sformatf("%s(%s)::insert_phase() inserted phase %s before phase %s",this.get_object_name(),this.get_typename(),phase_name,before_name));
      return 1;
   end
   else
      return 0;
endfunction:insert_phase

task vmm_timeline::delay_task(string name,
                              int unsigned delay,
			      ref bit running_phase_thread_done);
 int new_delay = -1;

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
       wait(running_phase_thread_done==1);
    end
 join_any
 disable fork;

 if(new_delay!= -1 && running_phase_thread_done!=1) begin
       delay_task(name,this.timeout_for_phases[name],running_phase_thread_done);
 end
endtask:delay_task

task vmm_timeline::wait_child_object_to_finish_phase(string name, 
                                                     vmm_object obj);
   vmm_timeline tl,tl2;
   vmm_object   child,child2;
   vmm_unit   mod1,mod2;
   int i = 0;

    /*don't wait for phase completion for timelines/units 
      1) whose timeline has not just started (newly added child 
         in this phase (typically in build) itself)
      2) whose timeline doesn't have this particular phase (deleted etc.) */
	  
   /* wait for completion of timeline's own phase */
   if (obj!= null && $cast(tl, obj)) begin
      bit dont_wait = (  (!tl.phase_impls.exists(name)) || 
                         ( (tl.get_previous_phase_name(name) != "^" 
	                        && tl.get_previous_phase_name(name) != "?")  
			   && (!tl.phase_impls[tl.get_previous_phase_name(name)].is_phase_done() 
			        && !tl.phase_impls[tl.get_previous_phase_name(name)].abort_done)) ); 
      if (!dont_wait) begin
         `vmm_debug(tl.log,`vmm_sformatf( "Waiting for execution to finish for phase %s ",name));
         wait(tl.phase_executed[name]==1);
         `vmm_debug(tl.log,`vmm_sformatf( "Wait over for execution of phase %s ",name));
      end
   end
   
   /* wait for completion of all root units */
   if ( (!$cast(tl,obj)) && $cast(mod2, obj)) begin
      /*don't wait for phase completion for units which is 
      disabled and reset phase is executed */
      bit dont_wait = (!mod2.is_unit_enabled() && mod2.phase_executed["reset"]) ;
      if(!mod2.is_implicitly_phased()) return;
      if(!dont_wait) begin
         `vmm_debug(mod2.log,`vmm_sformatf( "Waiting for execution to finish for phase %s ",name));
         wait(mod2.phase_executed[name]==1);
         `vmm_debug(mod2.log,`vmm_sformatf( "Wait over for execution of phase %s ",name));
      end
   end

  /* wait for completion of all unit type children */
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if($cast(mod1,child) && (!$cast(tl2,child)) )
	     this.wait_child_object_to_finish_phase(name,mod1);
      child = obj.get_nth_child(i++);
   end
endtask:wait_child_object_to_finish_phase
