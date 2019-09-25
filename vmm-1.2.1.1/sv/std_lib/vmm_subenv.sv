// //////////////////////////////////////////// 
// Class: vmm_subenv
//
// This is a base class used to encapsulate a reusable sub-environment.
// 
// Function: new 
// 
// Creates a new instance of this base class with the specified name and instance name.
// The specified name and instance names are used as the name and instance names of the log
// class property. 
// The specified end-of-test consensus object is assigned to the end_test class property,
// and may be used by the sub-environment to indicate that it opposes or consents to the
// ending of the test. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      function new(string name,string inst, 
//|              vmm_consensus end_test, vmm_object parent = null);
//|         super.new(name,inst,end_test, parent);
//|      endfunction
//|   endclass
function vmm_subenv::new(string         name,
                         string         inst,
                         `VMM_CONSENSUS end_test
                         `VMM_SUBENV_BASE_NEW_EXTERN_ARGS);
`ifdef VMM_SUBENV_BASE_NEW_CALL
   vmm_unit _temp_unit;
   super.new(`VMM_SUBENV_BASE_NEW_CALL);
`endif
`ifdef VMM_SUBENV_BASE_NEW_CALL
   if($cast(_temp_unit,this)) begin
      if(_temp_unit.log == null )
	     this.log =  new(name,this.get_object_hiername());
      else
		 this.log =  _temp_unit.log;
   end 
   else
      this.log = new(name, get_object_hiername());
`else
      this.log = new(name,inst);
`endif
   this.end_test = end_test;
endfunction: new


function string vmm_subenv::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sSub-Environment %s(%s): ", prefix,
            this.log.get_name(), this.log.get_instance());
   return psdisplay;
endfunction


function vmm_consensus vmm_subenv::get_consensus();
   return this.end_test;
endfunction


function void vmm_subenv:: configured();
   this.state = CONFIGURED;
endfunction: configured


// //////////////////////////////////////////// 
// 
// Task: start 
// 
// Starts the sub-environment. An error is reported, if this method is called before the
// sub-environment and DUT is reported as configured to the sub-environment base class,
// using the <vmm_consensus::unregister_voter> method. 
// A stopped sub-environment may be restarted. 
// The base implementation must be called using the super.start() method, by any extension
// of this method in a user-defined extension of this base class. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      virtual task start()
//|         super.start();
//|         this.my_xactor.start_xactor();
//|      endtask
//|   endclass
task vmm_subenv::start();
`ifdef __VMM_MSGLOG
   string stream_name, msg_name, msg_header,msg_body;
`endif

   if (this.state == NEWED) begin
      `vmm_error(this.log, "Sub-environment started before being configured");
   end
   this.state = STARTED;
endtask: start


task vmm_subenv::stop();
   if (this.state != STARTED) begin
      `vmm_warning(this.log, "Attempting to stop a sub-environment that has not been started");
   end
   this.state = STOPPED;
endtask: stop


task vmm_subenv::reset(vmm_env::restart_e kind = vmm_env::FIRM);
   this.state = STOPPED;
endtask: reset


// //////////////////////////////////////////// 
// Task: cleanup 
// 
// Stops the sub-environment (if not already stopped), and then verifies any end-of-test
// conditions. 
// The base implementation must be called using the super.cleanup(), by any extension
// of this method, in a user-defined extension of this base class. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      virtual task cleanup()
//|         super.cleanup();
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_subenv::cleanup();
   if (this.state != STOPPED) begin
      `vmm_warning(this.log, "Attempting to clean-up a sub-environment that has not been stopped");
   end
   this.state = CLEANED;
endtask: cleanup
   

// //////////////////////////////////////////// 
// 
// Task: report 
// 
// Reports status, coverage, or statistical information collected by the sub-environment,
// but not pass or fail of the test or sub-environment. 
// This method needs to be extended. It may also be invoked multiple times during the simulation.
// 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      virtual function void report()
//|         super.report();
//|         ...
//|      endfunction
//|      ...
//|   endclass
function void vmm_subenv::report();
endfunction: report

// //////////////////////////////////////////// 
// Function: do_psdisplay 
// 
// This method overrides the default implementation of the <psdisplay>
// method, created by the vmm_subenv shorthand macros. If defined, it will be used instead
// of the default implementation. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|     `vmm_subenv_member_begin( my_vmm_subenv)
//|         ...
//|      `vmm_subenv_member_end( my_vmm_subenv)
//|      virtual function string do_psdisplay(string prefix = "");
//|         $sformat(do_psdisplay,"%s Printing sub environment
//|             members \n",prefix);
//|         ...
//|      endfunction
//|      ...
//|   endclass
function string vmm_subenv::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction


// //////////////////////////////////////////// 
// 
// Task: do_vote 
// 
// This method overrides the default implementation of the voter registration, created
// by the vmm_subenv shorthand macros. If defined, it will be used instead of the default
// implementation. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      `vmm_subenv_member_begin( my_vmm_subenv)
//|         ...
//|      `vmm_subenv_member_end( my_vmm_subenv)
//|      protected virtual task do_vote();
//|         //Register with this.end_vote
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_subenv::do_vote();
   this.__vmm_done_user = 0;
endtask


// //////////////////////////////////////////// 
// 
// Task: do_start 
// 
// This method overrides the default implementation of the <start> method
// created by the vmm_subenv shorthand macros. If defined, it will be used instead of the
// default implementation. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      `vmm_subenv_member_begin( my_vmm_subenv)
//|         ...
//|      `vmm_subenv_member_end( my_vmm_subenv)
//|      protected virtual task do_start();
//|         //start operations
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_subenv::do_start();
   this.__vmm_done_user = 0;
endtask


// //////////////////////////////////////////// 
// 
// Task: do_stop 
// 
// This method overrides the default implementation of the <stop> method
// created by the vmm_subenv shorthand macros. If defined, it will be used instead of the
// default implementation. 
// 
//|   
//|   class my_vmm_subenv extends vmm_subenv;
//|      ...
//|      `vmm_subenv_member_begin( my_vmm_subenv)
//|         ...
//|      `vmm_subenv_member_end( my_vmm_subenv)
//|      protected virtual task do_stop();
//|         //stop operations
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_subenv::do_stop();
   this.__vmm_done_user = 0;
endtask


task vmm_subenv::do_reset(vmm_env::restart_e kind);
   this.__vmm_done_user = 0;
endtask
