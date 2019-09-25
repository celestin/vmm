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

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_phase_impl extends vmm_phase;
   vmm_phase_def defs[$];
   function new(string name, vmm_timeline parent);
      super.new(name, parent);
   endfunction:new
endclass

  //
  // 
  //

// //////////////////////////////////////////// 
// Class: vmm_function_phase_def
//
// Function: is_function_phase 
// 
// Returns true, if this phase is executed by calling the <vmm_phase_def::run_function_phase>
// method. Otherwise, it returns false. 
// 
//|   virtual class user_function_phase_def #( 
//|         user_function_phase_def) extends       vmm_topdown_function_phase_def;
//|      function bit is_function_phase();
//|         return 1;
//|      endfunction:is_function_phase 
//|   endclass
function bit vmm_function_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

// //////////////////////////////////////////// 
// Function: is_task_phase 
// 
// Returns true, if this phase is executed by calling the <vmm_phase_def::run_task_phase>
// method. Otherwise, it returns false. 
// 
//|   virtual class user_task_phase_def #( user_task_phase_def) 
//|         extends vmm_fork_task_phase_def;
//|      function bit is_task_phase();
//|         return 1;
//|      endfunction:is_task_phase 
//|   endclass 
function bit vmm_function_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase


// //////////////////////////////////////////// 
// Task: run_task_phase 
// 
// Executes the task phase, under the specified name on the specified root object. This
// method must be overridden if the <vmm_phase_def::is_task_phase> method returns
// true. 
// The argument log is the message interface instance to be used by the phase for reporting
// information. 
// 
//|   virtual class user_task_phase_def #( user_task_phase_def)
//|         extends vmm_fork_task_phase_def;
//|      function bit is_task_phase();
//|         return 1;
//|      endfunction:is_task_phase
//|      task run_task_phase(string name, vmm_object root, 
//|            vmm_log log);
//|         `vmm_note(log,`vmm_sformatf(
//|            "Executing phase %s for %s", name, 
//|            root.get_object_name());
//|      endtask
//|    
//|   endclass
task vmm_function_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase

// //////////////////////////////////////////// 
// Class: vmm_topdown_function_phase_def
//
// Function: run_function_phase 
// 
// Implementation of the function phase on an object of the specified type. 
// You can choose to execute some non-delay processes of the specified object in this method,
// of a new phase definition class extended from this class. 
// 
//|   class udf_phase_def extends vmm_topdown_function_phase_def;
//|      function void run_function_phase(vmm_unit un1);
//|         un1.my_method();
//|      endfunction
//|   endclass
function void vmm_topdown_function_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   vmm_object   child;
   vmm_timeline tl,tl2;
   vmm_unit     mod1,mod2,mod3;
   vmm_subenv   subenv;
   T            T_obj;
   int i;

   //nothing to do for units with phasing disabled
   if ($cast(mod2,obj)) begin
      if(!mod2.is_implicitly_phased()) return;
   end

   if ($cast(T_obj, obj)) begin
      vmm_timeline tl;
      this.do_function_phase(T_obj);
      if($cast(tl,T_obj))  
         tl.update_for_current_phase_counter(name);
      if ($cast(mod2,T_obj)) begin
         mod2.phase_executed[name]=1;
      end
   end
   /* if the user parametrise the phase with other than vmm_unit then to trigger
   timeline phase completion for those phases */
   else if ($cast(mod3, obj)) begin
      mod3.phase_executed[name]=1;
   end

  /* return if the object is subenv derived, as are not implicitly phasing it's children */
   if ($cast(subenv, obj)) begin
     return;
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
               if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                  void'(log.text(`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",
                  name,mod1.get_object_name(),mod1.get_typename())));
                  log.end_msg();
                end
	       mod1.override_phase_defs[name].run_function_phase(name, mod1, log);
	    end
	    else this.run_function_phase(name, mod1, log);
	 end
      end
      else this.run_function_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
endfunction:run_function_phase
// //////////////////////////////////////////// 
// Class: vmm_bottomup_function_phase_def
// 
// Function: run_function_phase 
// 
// Implementation of the function phase on an object of the specified type. You can choose
// to execute some non-delay processes of a specified object in this method, of a new phase
// definition class extended from this class. 
// 
//|   class udf_phase_def extends 
//|         vmm_bottomup_function_phase_def;
//|      function void run_function_phase(vmm_unit un1);
//|         un1.my_method(); 
//|      endfunction
//|   endclass
function void vmm_bottomup_function_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   vmm_object   child;
   vmm_timeline tl,tl2;
   vmm_unit   mod1,mod2,mod3;
   vmm_subenv   subenv;
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

  /* return if the object is subenv derived, as are not implicitly phasing it's children */
   if ($cast(subenv, obj)) begin
     return;
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
               if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                  void'(log.text(
                  `vmm_sformatf( "Using new definition of phase %s for %s(%s) ",
                  name,mod1.get_object_name(),mod1.get_typename())));
                  log.end_msg();
                end
	       mod1.override_phase_defs[name].run_function_phase(name, mod1, log);
	    end
	    else this.run_function_phase(name, mod1, log);
	 end
	 end
      else this.run_function_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
   if ($cast(T_obj, obj)) begin
      vmm_timeline tl;
      this.do_function_phase(T_obj);
      if($cast(tl,T_obj))  
         tl.update_for_current_phase_counter(name);
      if ($cast(mod2,T_obj))
         mod2.phase_executed[name]=1;
   end
endfunction:run_function_phase

// //////////////////////////////////////////// 
// Class: vmm_task_phase_def
// 
// Function: is_function_phase 
// 
// Returns true, if this phase is executed by calling the <vmm_phase_def::run_function_phase>
// method. Otherwise, it returns false. 
// 
//|   virtual class user_function_phase_def #( 
//|         user_function_phase_def) extends       vmm_topdown_function_phase_def;
//|      function bit is_function_phase();
//|         return 1;
//|      endfunction:is_function_phase 
//|   endclass
function bit vmm_task_phase_def::is_function_phase();
   return 0;
endfunction:is_function_phase

// //////////////////////////////////////////// 
// Function: is_task_phase 
// 
// Returns true, if this phase is executed by calling the <vmm_phase_def::run_task_phase>
// method. Otherwise, it returns false. 
// 
//|   virtual class user_function_phase_def #( 
//|         extends vmm_fork_task_phase_def;
//|      function bit is_task_phase();
//|         return 1;
//|      endfunction:is_task_phase 
//|   endclass 
function bit vmm_task_phase_def::is_task_phase();
   return 1;
endfunction:is_task_phase

// //////////////////////////////////////////// 
// Function: run_function_phase 
// 
// Executes the function phase, under the specified name on the specified object. This
// method must be overridden, if the <vmm_phase_def::is_function_phase> method returns
// true. 
// The argument log is the message interface instance to be used by the phase for reporting
// information. 
// 
//|   virtual class user_function_phase_def #( 
//|         user_function_phase_def) 
//|         extends vmm_topdown_function_phase_def;
//|      function bit is_function_phase();
//|         return 1;
//|      endfunction:is_function_phase 
//|   
//|      function run_function_phase(string name, 
//|            vmm_object root, vmm_log log);
//|         `vmm_note(log,`vmm_sformatf(
//|            "Executing phase %s for %s", name, 
//|            root.get_object_name());
//|      endfuction
//|   endclass 
function void vmm_task_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_function_phase() called instead of %s::run_task_phase()",
                            this.get_typename(), this.get_typename()));
endfunction:run_function_phase

// //////////////////////////////////////////// 
// Class: vmm_fork_task_phase_def
// 
// Task: run_task_phase 
// 
// Implementation of the task phase on an object of the specified type. You can choose to
// execute time-consuming processes in this method, of a new phase definition class extended
// from this class. 
// 
//|   class udf_phase_def extends vmm_fork_task _phase_def;
//|      task run_task_phase(vmm_unit un1); 
//|        un1.my_method(); 
//|      endtask
//|   endclass
task vmm_fork_task_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   vmm_object   child;
   vmm_timeline tl2;
   vmm_unit     mod2,mod3;
   vmm_subenv   subenv;
   T            T_obj;
   int i;

   //nothing to do for units with phasing disabled
   if ($cast(mod2,obj)) begin
      if(!mod2.is_implicitly_phased()) return;
   end

   if ($cast(T_obj, obj)) begin
      fork
         begin
	    vmm_timeline tl;
            this.do_task_phase(T_obj);
            if($cast(tl,T_obj))  
               tl.update_for_current_phase_counter(name);
	    if ($cast(mod2,T_obj)) begin
               if(name == "run_test")
                   mod2.vote.wait_for_consensus();
	       tl = mod2.get_timeline();
               if (mod2.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                  void'(mod2.log.text(
                  `vmm_sformatf( "wait on child unit objects for phase %s",name)));
                  mod2.log.end_msg();
               end
	       begin
	          tl.phase_wait_finish(name,mod2);
	       end
               if (mod2.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                  void'(mod2.log.text(
                  `vmm_sformatf( "wait done on child unit objects for phase %s",name)));
                  mod2.log.end_msg();
               end
	       if(!tl.do_abort_phase) mod2.phase_executed[name]=1;
            end
	 end
      join_none
   end

   /* if the user parametrise the phase with other than vmm_unit then to trigger
   timeline phases for those phases */
   else if ($cast(mod3, obj)) begin
    fork 
     begin
      vmm_timeline tl;
      if(name == "run_test")
          mod3.vote.wait_for_consensus();

       tl = mod3.get_timeline();
       if (mod3.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
          void'(mod3.log.text(
          `vmm_sformatf( "wait on child unit objects for phase %s",name)));
          mod3.log.end_msg();
       end
       begin
         tl.phase_wait_finish(name,mod3);
       end
       if (mod3.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
          void'(mod3.log.text(
          `vmm_sformatf( "wait done on child unit objects for phase %s",name)));
          mod3.log.end_msg();
       end
       if(!tl.do_abort_phase) mod3.phase_executed[name]=1;
       else 
          if (tl.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
             void'(tl.log.text(
             `vmm_sformatf("phasing - Abort for current executing phase \"%s\" is executed for this unit timeline",name)));
             tl.log.end_msg();
          end
     end
    join_none
   end

  /* return if the object is subenv derived, as are not implicitly phasing it's children */
   if ($cast(subenv, obj)) begin
     return;
   end

   child = obj.get_nth_child(i++);
   while (child != null) begin
      vmm_unit   mod1;
      vmm_timeline tl;
      if ($cast(tl, child)) begin
         tl.not_self_phased = 1;
         fork
	   begin
            tl.run_phase(name);
	   end
	 join_none
      end
      else if($cast(mod1,child)) begin
         vmm_timeline t2;
	 t2 = mod1.get_timeline();
	 if(!mod1.is_unit_enabled() && mod1.phase_executed["reset"]) ;
         else begin
	    if(mod1.override_phase_defs.exists(name)) begin
                if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
                   void'(log.text(
                   `vmm_sformatf( "Using new definition of phase %s for %s(%s) ",
                   name,mod1.get_object_name(),mod1.get_typename())));
                   log.end_msg();
                end
	       mod1.override_phase_defs[name].run_task_phase(name, mod1, log);
	    end
	    else begin
	       fork
	          this.run_task_phase(name, mod1, log);
	       join_none
	    end
	 end
      end
     // else  this.run_task_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
endtask:run_task_phase

function bit vmm_null_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_null_phase_def::is_task_phase();
   return 1;
endfunction:is_task_phase

function void vmm_null_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
endfunction:run_function_phase
task vmm_null_phase_def::run_task_phase(string     name,
                            vmm_object obj,
                            vmm_log    log);
   vmm_unit  mod2;
   if ($cast(mod2,obj)) begin
       mod2.phase_executed[name] = 1;
   end
endtask:run_task_phase


function vmm_xactor_phase_def_base::new(string name = "/./",
                                   string inst = "/./");
   this.name = name;
   this.inst = inst;
endfunction:new

function bit vmm_xactor_phase_def_base::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_xactor_phase_def_base::is_task_phase();
   return 0;
endfunction:is_task_phase

task vmm_xactor_phase_def_base::run_task_phase(string     name,
                                 vmm_object obj,
                                 vmm_log    log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));
endtask:run_task_phase

function vmm_xactor_phase_def::new(string name = "/./",
                                   string inst = "/./");
   super.new(name, inst);
endfunction:new

function void vmm_xactor_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   //nothing to do for units with phasing disabled
   vmm_xactor xactor;
   if ($cast(xactor,obj)) begin
`ifdef VMM_12_UNDERPIN_VMM_XACTOR
      if(!obj.is_implicitly_phased()) return;
`endif
   end
   else begin
      `foreach_vmm_xactor(T, this.name, this.inst)
         this.do_function_phase(xact);
   end
endfunction:run_function_phase

function void vmm_root_function_phase_def::run_function_phase(string     name,
                                         vmm_object obj,
                                         vmm_log    log);
   vmm_unit     unit;
   T            T_obj;

   //nothing to do for units with phasing disabled
   if ($cast(unit,obj)) begin
      if((!unit.is_implicitly_phased()) ||
         (unit.get_parent_object() != null)) return;
   end

   if ($cast(T_obj, obj)) begin
      vmm_timeline tl;
      this.do_function_phase(T_obj);
      if($cast(tl,T_obj))
         tl.update_for_current_phase_counter(name);
      if ($cast(unit,T_obj)) begin
         unit.phase_executed[name]=1;
      end
   end
   else if ($cast(unit, obj)) begin
      unit.phase_executed[name]=1;
   end
endfunction : run_function_phase
