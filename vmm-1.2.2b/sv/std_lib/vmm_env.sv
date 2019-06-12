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
// Class: vmm_env
//
// A base class used to implement verification environments
//
// Function: new
// 
// Creates an instance of the verification environment, with the specified name. The
// name is used as the name of the message service interface. 
// 
function vmm_env::new(string name = "Verif Env"
                      `VMM_ENV_BASE_NEW_EXTERN_ARGS);
   int initial_seed;

`ifdef VMM_ENV_BASE_NEW_CALL
   super.new(`VMM_ENV_BASE_NEW_CALL);
`endif


`ifdef VMM_12_UNDERPIN_VMM_ENV
   this.log    = new(name, this.get_object_hiername());
   begin
      int i = 0;
      int multiple_env_instance;
      string root_env_names;
      vmm_object root = vmm_object::get_nth_root(i++);
      while (root != null) begin
          vmm_env root_env_obj;
          if($cast(root_env_obj, root) ) begin
	     multiple_env_instance++;
	     $sformat(root_env_names,"%s \n %s",root_env_names,root_env_obj.get_object_name());
          end
          root = vmm_object::get_nth_root(i++);
      end
      if(multiple_env_instance > 1) begin
	 `vmm_warning(this.log, `vmm_sformatf("Multiple instance found for vmm_env type objects ,it is advised to have one top vmm_env instance and convert other vmm_env instances to subenv.\n Following are all instances names %s",root_env_names)); 
      end
   end

`else
   this.log    = new(name, "");
`endif
`ifdef VMM_TR_RECORD
   this.top_stream = vmm_tr_record::open_stream(this.log.get_instance(), "Env", vmm_debug::TRACE_SEV);
`endif //VMM_TR_RECORD

   if ($value$plusargs("ntb_random_seed=%d", initial_seed)) begin
      `vmm_note(this.log, `vmm_sformatf("Initial random seed is %0d", initial_seed));
   end

   if (this.singleton == null) this.singleton = this;
   else begin
      `vmm_warning(log, "Multiple vmm_env instances exists. There should be only on top-level vmm_env controlling the overall verification environment phasing. Use vmm_subenv to encapsulate reusable environments.");
   end

   this.step = 0;

   this.notify = new(this.log);
`ifdef VMM_12_UNDERPIN_VMM_DATA
   `ifdef VMM_12_UNDERPIN_VMM_ENV
   `ifdef VMM_12_UNDERPIN_VMM_NOTIFY
       this.notify.set_parent(this);
   `endif
   `endif
`endif

   void'(this.notify.configure(GEN_CFG,      vmm_notify::ON_OFF));
   void'(this.notify.configure(BUILD,        vmm_notify::ON_OFF));
   void'(this.notify.configure(RESET_DUT,    vmm_notify::ON_OFF));
   void'(this.notify.configure(CFG_DUT,      vmm_notify::ON_OFF));
   void'(this.notify.configure(START,        vmm_notify::ON_OFF));
   void'(this.notify.configure(RESTART,      vmm_notify::ON_OFF));
   void'(this.notify.configure(WAIT_FOR_END, vmm_notify::ON_OFF));
   void'(this.notify.configure(STOP,         vmm_notify::ON_OFF));
   void'(this.notify.configure(CLEANUP,      vmm_notify::ON_OFF));
   void'(this.notify.configure(REPORT,       vmm_notify::ON_OFF));

   this.reset_rng_state = 0;
   this.thread_rng_state_after_new = get_randstate();

   this.soft_restart = 0;
   this.soft_restartable = 0;

   this.end_vote = new(name, "End-of-test Consensus");
`ifdef VMM_12_UNDERPIN_VMM_DATA
`ifdef VMM_12_UNDERPIN_VMM_ENV
   `ifdef VMM_12_UNDERPIN_VMM_CONSENSUS
      this.end_vote.set_parent(this);
   `endif
`endif
`endif
endfunction: new


function string vmm_env::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sEnvironment %s(%s): ", prefix, 
            this.log.get_name(), this.log.get_instance());
   return psdisplay;
endfunction


// //////////////////////////////////////////// 
// 
// Task: run 
// 
// Runs all remaining steps of the simulation, including <stop(), cleanup(),
// and report>. This method must be explicitly invoked in the test programs.
// 
// 
task vmm_env::run();
   if (this.step == 0 ||
       this.step == RESTARTED) this.pre_test();

   if (this.step < CLEANUP) this.cleanup();
   if (this.step != CLEANUP) begin
      `vmm_fatal(this.log, "Extension of vmm_env::cleanup() did not call super.cleanup().");
   end
   this.report();
endtask: run


task vmm_env::reset_env(restart_e kind);
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text({"Resetting environment (", kind.name(), ")..."}));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.top_stream, "reset_env", "");
`endif //VMM_TR_RECORD
endtask: reset_env


task vmm_env::power_on_reset();
   this.hw_reset();
endtask: power_on_reset


task vmm_env::hw_reset();
endtask: hw_reset


task vmm_env::power_up();
   // All ON by default
endtask: power_up


task vmm_env::pre_test();
   if (this.step == 0) begin
      this.cfg_dut();
      if (this.step != CFG_DUT) 
         `vmm_fatal(this.log, "Extension of vmm_env::cfg_dut() did not call super.cfg_dut().");

      // Save the seed for the main program thread
      this.thread_rng_state_after_pre_test = get_randstate();
      // Save the RNG state for the entire environment as built
      this.save_rng_state();
   
      // Make sure the saved seed are the one that are going
      // to be used when starting the environment, even if
      // some components are manually replaced in the test
      this.reset_rng_state = 1;
   end
   else if (this.step == RESTARTED) begin
      this.step = CFG_DUT;
   end
   else if (this.step <= CFG_DUT) begin
      `vmm_fatal(this.log, "vmm_env::pre_test() was not the first simulation step in simulation flow.");
   end
   else if (this.step > CFG_DUT) begin
      `vmm_fatal(this.log, "vmm_env::pre_test() called too late in simulation flow.");
   end

   set_randstate(this.thread_rng_state_after_pre_test);
   this.soft_restartable = 1;
   this.soft_restart = 0;
endtask: pre_test


function void vmm_env::gen_cfg();
   if (this.soft_restart) begin
     `vmm_fatal(this.log, "Cannot run a tests that invokes vmm_env::gen_cfg after a soft restart...");
   end

   this.step = GEN_CFG;
   this.notify.indicate(GEN_CFG);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Generating test configuration..."));
      this.log.end_msg();
   end

`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.top_stream, "gen_cfg", "");
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD
endfunction: gen_cfg


// //////////////////////////////////////////// 
// Function: build 
// 
// Builds the verification environment, according to the value of the test configuration
// descriptor. If this method is not explicitly invoked in the test program, it will be
// implicitly invoked by the <reset_dut> method. 
// 
//|   
//|   class my_test extends vmm_test;
//|      ...
//|      virtual task run(vmm_env env);
//|         tb_env my_env;
//|         $cast(my_env, env);
//|         my_env.build();
//|         my_env.gen[0].start_xactor();
//|         my_env.run();
//|      endtask
//|   endclass
function void vmm_env::build();

   if (this.soft_restart) begin
      `vmm_fatal(this.log, "Cannot run a tests that invokes vmm_env::build after a soft restart...");
   end

   if (this.step < GEN_CFG) this.gen_cfg();
   if (this.step != GEN_CFG) begin
      `vmm_fatal(this.log, "Extension of vmm_env::gen_cfg() did not call super.gen_cfg().");
   end

   this.step = BUILD;
   this.notify.indicate(BUILD);
   
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Building verification environment..."));
      this.log.end_msg();
   end

`ifdef VMM_12_UNDERPIN_VMM_DATA
`ifdef VMM_12_UNDERPIN_VMM_ENV
   `ifdef VMM_12_UNDERPIN_VMM_CONSENSUS
   if (!vmm_consensus::is_register_consensus()) begin
      vmm_simulation::register_unit_consensus();
   end
   `endif
`endif
`endif

`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.top_stream, "build", "");
   vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD
endfunction: build


// //////////////////////////////////////////// 
// 
// Task: reset_dut 
// 
// Physically resets the DUT to make it ready for configuration. If this method is not explicitly
// invoked in the test program, it will be implicitly invoked by the <cfg_dut>
// method. 
// 
task vmm_env::reset_dut();

   if (this.soft_restart) begin
      `vmm_fatal(this.log, "Cannot run a tests that invokes vmm_env::cfg_dut_t after a soft restart...");
   end

   if (_vmm_opts.get_bit("help", "Displays a list of all VMM run-time options queried so far")) begin
      _vmm_opts.get_help();
      $finish;
   end

   if (this.step < BUILD) this.build();
   if (this.step != BUILD) begin
      `vmm_fatal(this.log, "Extension of vmm_env::build() did not call super.build().");
   end

   this.step = RESET_DUT;
   this.notify.indicate(RESET_DUT);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Reseting DUT..."));
      this.log.end_msg();
   end
   this.power_on_reset();
`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.top_stream, "reset_dut", "");
`endif //VMM_TR_RECORD

endtask: reset_dut


// //////////////////////////////////////////// 
// 
// Task: cfg_dut 
// 
// Configures the DUT, according to the value of the test configuration descriptor. If
// this method is not explicitly invoked in the test program, it will be implicitly invoked
// by the <start> method. 
// 
task vmm_env::cfg_dut();

   if (this.soft_restart) begin
      `vmm_fatal(this.log, "Cannot run a tests that invokes vmm_env::cfg_dut_t after a soft restart...");
   end

   if (this.step < RESET_DUT) this.reset_dut();
   if (this.step != RESET_DUT) begin
      `vmm_fatal(this.log, "Extension of vmm_env::reset_dut() did not call super.reset_dut().");
   end

   this.step = CFG_DUT;
   this.notify.indicate(CFG_DUT);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Configuring..."));
      this.log.end_msg();
   end
   this.power_up();
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "cfg_dut", "");
`endif //VMM_TR_RECORD
endtask: cfg_dut


// //////////////////////////////////////////// 
// 
// Task: start 
// 
// Starts all the components of the verification environment to start the actual test.
// If this method is not explicitly invoked in the test program, it will be implictly invoked
// by the <wait_for_end> method. 
// 
task vmm_env::start();

   if (this.step < CFG_DUT) this.cfg_dut();
   if (this.step != CFG_DUT) begin
      `vmm_fatal(this.log, "Extension of vmm_env::cfg_dut() did not call super.cfg_dut().");
   end

   this.step = START;
   this.notify.indicate(START);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Starting verification environment..."));
      this.log.end_msg();
   end

   if (this.reset_rng_state) begin
      this.restore_rng_state();
      this.reset_rng_state = 0;
   end
   else this.save_rng_state();
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "start", "");
`endif //VMM_TR_RECORD
endtask: start


task vmm_env::wait_for_end();

   if (this.step < START) this.start();
   if (this.step != START) begin
      `vmm_fatal(this.log, "Extension of vmm_env::start() did not call super.start().");
   end

   this.step = WAIT_FOR_END;
   this.notify.indicate(WAIT_FOR_END);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Waiting for end of test..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "wait_for_end", "");
`endif //VMM_TR_RECORD
endtask: wait_for_end


// //////////////////////////////////////////// 
// 
// Task: stop 
// 
// Terminates all components of the verification environment to terminate the simulation,
// cleanly. If this method is not explicitly invoked in the test program, it will be implicitly
// invoked by the <cleanup> method. 
// 
task vmm_env::stop();

   if (this.step < WAIT_FOR_END) this.wait_for_end();
   if (this.step != WAIT_FOR_END) begin
      `vmm_fatal(this.log, "Extension of vmm_env::wait_for_end() did not call super.wait_for_end().");
   end

   this.step = STOP;
   this.notify.indicate(STOP);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Stopping verification environment..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "stop", "");
`endif //VMM_TR_RECORD
endtask: stop


// //////////////////////////////////////////// 
// 
// Task: cleanup 
// 
// Performs clean-up operations to terminate the simulation, gracefully. Clean-up
// operations may include, letting the DUT drain off all buffered data, reading statistics
// registers in the DUT, and sweeping the scoreboard for leftover expected responses.
// If this method is not explicitly invoked in the test program, it will be implicitly invoked
// by the <run> method. 
// 
task vmm_env::cleanup();

   if (this.step < STOP) this.stop();
   if (this.step != STOP) begin
      `vmm_fatal(this.log, "Extension of vmm_env::stop() did not call super.stop().");
   end

   this.step = CLEANUP;
   this.notify.indicate(CLEANUP);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Cleaning up..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "cleanup", "");
`endif //VMM_TR_RECORD
endtask: cleanup


task vmm_env::restart(bit reconfig = 0);
fork begin
   if (!reconfig && !this.soft_restartable) begin
      `vmm_fatal(this.log, "Cannot soft-restart after test that did not call vmm_env::pre_test().");
   end

   this.reset_env((reconfig) ? HARD : SOFT);

   // Only go to the end-of-test on SOFT or HARD restart
   if (this.step < CLEANUP) this.cleanup();
   if (this.step != CLEANUP) begin
      `vmm_fatal(this.log, "Extension of vmm_env::cleanup() did not call super.cleanup().");
   end

   this.notify.indicate(RESTART);
   
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Restarting..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "restart", "");
`endif //VMM_TR_RECORD

   this.notify.reset(START);
   this.notify.reset(RESTART);
   this.notify.reset(WAIT_FOR_END);
   this.notify.reset(STOP);
   this.notify.reset(CLEANUP);
   this.notify.reset(REPORT);

   if (reconfig) begin
      this.step = 0;
      this.notify.reset(GEN_CFG);
      this.notify.reset(BUILD);
      this.notify.reset(RESET_DUT);
      this.notify.reset(CFG_DUT);
      this.soft_restart = 0;
      // Kill all sub-threads
      disable fork;
   end
   else begin
      this.step = RESTARTED;
      this.reset_rng_state = 1;
      this.soft_restart = 1;
   end
  end 
join
   set_randstate(this.thread_rng_state_after_new);
endtask: restart


task vmm_env::restart_test();

   this.reset_env(FIRM);

   this.notify.indicate(RESTART);

   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Restarting test..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "restart_test", "");
`endif //VMM_TR_RECORD

   this.notify.reset(RESET_DUT);
   this.notify.reset(CFG_DUT);
   this.notify.reset(START);
   this.notify.reset(RESTART);
   this.notify.reset(WAIT_FOR_END);
   this.notify.reset(STOP);
   this.notify.reset(CLEANUP);
   this.notify.reset(REPORT);

   this.step = BUILD;
endtask: restart_test


// //////////////////////////////////////////// 
// 
// Task: report 
// 
// Reports final success or failure of the test, and closes all files. If this method is
// not explicitly invoked in the test program, it will be implicitly invoked by the <run>
// method. 
// 
task vmm_env::report();
   this.log.report("/./", "/./");
   this.notify.indicate(REPORT);
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD
endtask: report

function void vmm_env::save_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Saving RNG state information..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "save_rng_state", "");
`endif //VMM_TR_RECORD
   this.thread_rng_state_before_start = get_randstate();
endfunction: save_rng_state


function void vmm_env::restore_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP , vmm_log::TRACE_SEV )) begin
      void'(this.log.text("Restoring RNG state information..."));
      this.log.end_msg();
   end
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
   vmm_tr_record::start_tr(this.top_stream, "restore_rng_state", "");
`endif //VMM_TR_RECORD
   set_randstate(this.thread_rng_state_before_start);
endfunction: restore_rng_state


// //////////////////////////////////////////// 
// Function: do_psdisplay 
// 
// This method overrides the default implementation of the <psdisplay> method
// that is created by the vmm_env shorthand macros. If defined, this method is used instead
// of the default implementation. 
// 
//|   
//|   class my_vmm_env extends vmm_env;
//|      ...
//|   
//|      virtual function string do_psdisplay(string prefix = "");
//|        $sformat(do_psdisplay,"%s Printing environment members",
//|           prefix);
//|         ...
//|      endfunction
//|      ...
//|   endclass
function string vmm_env::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction


// //////////////////////////////////////////// 
// 
// Task: do_vote 
// 
// This method overrides the default implementation of the voter registration that is
// created by the vmm_env shorthand macros. If defined, this method is used instead of
// the default implementation. 
// 
//|   
//|   class my_vmm_env extends vmm_env;
//|      ...
//|      protected virtual task do_vote();
//|         //Register with this.end_vote
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_env::do_vote();
   this.__vmm_done_user = 0;
endtask


// //////////////////////////////////////////// 
// 
// Task: do_start 
// 
// This method overrides the default implementation of the <start> method
// that is created by the vmm_env shorthand macros. If defined, this method is used instead
// of the default implementation. 
// 
//|   
//|   class my_vmm_env extends vmm_env;
//|      ...
//|      protected virtual task do_start();
//|         //start operations
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_env::do_start();
   this.__vmm_done_user = 0;
endtask


// //////////////////////////////////////////// 
// 
// Task: do_stop 
// 
// This method overrides the default implementation of the <stop> method that
// is created by the vmm_env shorthand macros. If defined, this method is used instead
// of the default implementation. 
// 
//|   
//|   class my_vmm_env extends vmm_env;
//|      ...
//|      protected virtual task do_stop();
//|         //stop operations
//|         ...
//|      endtask
//|      ...
//|   endclass
task vmm_env::do_stop();
   this.__vmm_done_user = 0;
endtask


task vmm_env::do_reset(vmm_env::restart_e kind);
   this.__vmm_done_user = 0;
endtask
