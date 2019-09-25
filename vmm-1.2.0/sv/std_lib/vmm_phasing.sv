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

class vmm_phase_impl extends vmm_phase;
   vmm_phase_def defs[$];
   function new(string name, vmm_timeline parent);
      super.new(name, parent);
   endfunction:new
endclass

  //
  // 
  //

function bit vmm_topdown_function_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_topdown_function_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase

function void vmm_topdown_function_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   vmm_object   child;
   vmm_timeline tl,tl2;
   vmm_unit     mod1,mod2,mod3;
   T            T_obj;
   int i;

   //nothing to do for units with phasing disabled
   if ($cast(mod2,obj)) begin
      if(!mod2.is_implicitly_phased()) return;
   end

   if ($cast(T_obj, obj)) begin
      this.do_function_phase(T_obj);
      if ($cast(mod2,T_obj)) begin
         mod2.phase_executed[name]=1;
      end
   end
   /* if the user parametrise the phase with other than vmm_unit then to trigger
   timeline phase completion for those phases */
   else if ($cast(mod3, obj)) begin
      mod3.phase_executed[name]=1;
   end

   i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
         tl.run_function_phase(name);
      end
      else if($cast(mod1,child))begin
         vmm_timeline t2;
	 t2 = mod1.get_timeline();
	 if(!mod1.is_unit_enabled() && mod1.phase_executed["reset"]) ;
         else begin
	    if(mod1.override_phase_defs.exists(name)) begin
	       `vmm_debug(log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,mod1.get_object_name(),mod1.get_typename()));
	       mod1.override_phase_defs[name].run_function_phase(name, mod1, log);
	    end
	    else this.run_function_phase(name, mod1, log);
	 end
      end
      else this.run_function_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
endfunction:run_function_phase

task vmm_topdown_function_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase

function bit vmm_bottomup_function_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_bottomup_function_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase

function void vmm_bottomup_function_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   vmm_object   child;
   vmm_timeline tl,tl2;
   vmm_unit   mod1,mod2,mod3;
   T            T_obj;
   int i;

   //nothing to do for units with phasing disabled
   if ($cast(mod2,obj)) begin
      if(!mod2.is_implicitly_phased()) return;
   end

   /* if the user parametrise the phase with other than vmm_unit then to trigger
   timeline phases for those phases */
   if ((!$cast(T_obj, obj)) && ($cast(mod3, obj))) begin
      mod3.phase_executed[name]=1;
   end


   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
         tl.run_function_phase(name);
      end
      else if($cast(mod1,child))begin
         vmm_timeline t2;
	 t2 = mod1.get_timeline();
	 if(!mod1.is_unit_enabled() && mod1.phase_executed["reset"]) ;
         else begin
	    if(mod1.override_phase_defs.exists(name)) begin
	       `vmm_debug(log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,mod1.get_object_name(),mod1.get_typename()));
	       mod1.override_phase_defs[name].run_function_phase(name, mod1, log);
	    end
	    else this.run_function_phase(name, mod1, log);
	 end
	 end
      else this.run_function_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
   if ($cast(T_obj, obj)) begin
      this.do_function_phase(T_obj);
         if ($cast(mod2,T_obj))
	     mod2.phase_executed[name]=1;
   end
endfunction:run_function_phase

task vmm_bottomup_function_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase

function bit vmm_fork_task_phase_def::is_function_phase();
   return 0;
endfunction:is_function_phase

function bit vmm_fork_task_phase_def::is_task_phase();
   return 1;
endfunction:is_task_phase

function void vmm_fork_task_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_function_phase() called instead of %s::run_task_phase()",
                            this.get_typename(), this.get_typename()));
endfunction:run_function_phase

task vmm_fork_task_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   vmm_object   child;
   vmm_timeline tl2;
   vmm_unit   mod1,mod2,mod3;
   T            T_obj;
   int i;

   //nothing to do for units with phasing disabled
   if ($cast(mod2,obj)) begin
      if(!mod2.is_implicitly_phased()) return;
   end

   if ($cast(T_obj, obj)) begin
      fork
         begin
            this.do_task_phase(T_obj);
	    if ($cast(mod2,T_obj))
	       mod2.phase_executed[name]=1;
	 end
      join_none
   end

   /* if the user parametrise the phase with other than vmm_unit then to trigger
   timeline phases for those phases */
   else if ($cast(mod3, obj)) begin
      mod3.phase_executed[name]=1;
   end

   child = obj.get_nth_child(i++);
   while (child != null) begin
      vmm_timeline tl;
      if ($cast(tl, child)) begin
         tl.run_phase(name);
      end
      else if($cast(mod1,child)) begin
         vmm_timeline t2;
	 t2 = mod1.get_timeline();
	 if(!mod1.is_unit_enabled() && mod1.phase_executed["reset"]) ;
         else begin
	    if(mod1.override_phase_defs.exists(name)) begin
	       `vmm_debug(log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,mod1.get_object_name(),mod1.get_typename()));
	       mod1.override_phase_defs[name].run_task_phase(name, mod1, log);
	    end
	    else this.run_task_phase(name, mod1, log);
	 end
      end
      else  this.run_task_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
endtask:run_task_phase

function bit vmm_null_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_null_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase

function void vmm_null_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
endfunction:run_function_phase
task vmm_null_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase


function vmm_xactor_phase_def::new(string name ,
                                   string inst );
   this.name = name;
   this.inst = inst;
endfunction:new

function bit vmm_xactor_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_xactor_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase

function void vmm_xactor_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   //nothing to do for units with phasing disabled
   vmm_xactor xactor;
   if ($cast(xactor,obj)) begin
      if(!xactor.is_implicitly_phased()) return;
   end
   else begin
      `foreach_vmm_xactor(T, this.name, this.inst)
         this.do_function_phase(xact);
   end
endfunction:run_function_phase
task vmm_xactor_phase_def::run_task_phase(string     name,
                                 vmm_object obj,
                                 vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase
