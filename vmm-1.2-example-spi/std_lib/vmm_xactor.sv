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


////////////////////////////////////////////////////////////
// Class: vmm_xactor
//
// This base class is to be used as the basis for all transactors, 
// including bus-functional models, monitors, and generators. 
//
// It provides a standard control mechanism expected in all transactors
//
////////////////////////////////////////////////////////////
  
////////////////////////////////////////////////////////////
// Function: new
// Creates an instance of the transactor base class, with the specified name, 
// instance name, and optional stream identifier. 
//
// The name and instance name are used to create the message service interface 
// in the <vmm_xactor::log> property, and the specified stream identifier is 
// used to initialize the <vmm_xactor::stream_id> property.
    
function vmm_xactor::new(string name,
                         string inst,
     	                 int    stream_id = -1
                         `VMM_XACTOR_BASE_NEW_EXTERN_ARGS);

`ifdef VMM_XACTOR_BASE_NEW_CALL
   vmm_unit _temp_unit;
   super.new(`VMM_XACTOR_BASE_NEW_CALL);
`endif

`ifdef VMM_XACTOR_BASE_NEW_CALL
   if($cast(_temp_unit,this)) begin
      if(_temp_unit.log == null)
         this.log =  new(name,inst); 
      else
		 this.log = _temp_unit.log;
   end
   else
	   this.log = new(name,inst);
`else
   this.log  = new(name, inst);
`endif
   this.notify = new(this.log);
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_NOTIFY
   `VMM_OBJECT_SET_PARENT(this.notify, this)
`endif
`endif

   void'(this.notify.configure(XACTOR_IDLE, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_BUSY, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_STARTED));
   void'(this.notify.configure(XACTOR_STOPPING, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_IS_STOPPED, vmm_notify::ON_OFF));
   void'(this.notify.configure(XACTOR_STOPPED));
   void'(this.notify.configure(XACTOR_RESET));

   this.is_stopped = 1;
   this.notify.indicate(XACTOR_IS_STOPPED);
   this.notify.indicate(XACTOR_IDLE);

   this.stream_id   = stream_id;

   this.start_it   = 0;
   this.stop_it    = 1;
   this.reset_it   = 0;
   this.n_threads_to_stop = -1;
   this.n_threads_stopped = 0;
   this.main_running = 0;

   // Dummy first entry in list of known transactors
   if (this._vmm_available_xactor.size() == 0) begin
      this._vmm_available_xactor.push_back(null);
   end
   this._vmm_available_xactor.push_back(this); 

   fork
      begin
      this.save_main_rng_state    = 1;
      this.restore_main_rng_state = 0;
      this.main_rng_state = get_randstate();

      while (1) begin
         this.main_running = 0;

         // wait to start
         while (!this.start_it) @(this.control_event);
         this.start_it = 0;
         this.stop_it  = 0;
         this.reset_it = 0;
         this.n_threads_to_stop = -1;
         this.n_threads_stopped = 0;
         this.is_stopped = 0;

         // We may be held back by on-going reset operation
         fork
            if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
               void'(this.log.text("Start delayed by on-going reset activity"));
               this.log.end_msg();
            end
         join_none

         while (this.reset_pending > 0) begin
            `vmm_fatal(this.log, "Pending resets not currently supported");
            // `wait(@(this.reset_pending)); // Not supported yet.
         end
         disable fork;

         //
         // Fork the main body
         //
               
         if (this.save_main_rng_state) begin
            this.main_rng_state = get_randstate();
         end
         if (this.restore_main_rng_state) begin
            set_randstate(main_rng_state);
         end
         this.save_main_rng_state    = 0;
         this.restore_main_rng_state = 0;

         fork
            begin
               if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV )) begin
                  void'(this.log.text("Started"));
                  this.log.end_msg();
               end

               this.is_stopped = 0;
               this.notify.reset(XACTOR_IDLE);
               this.notify.reset(XACTOR_IS_STOPPED);
               this.notify.indicate(XACTOR_BUSY);
               this.notify.indicate(XACTOR_STARTED);
               main();
            end

            begin
               // Check that super.main() was called in all
               // extensions of this class
               repeat(10) #0;
               if (!this.main_running) begin
                  `vmm_warning(this.log, "Virtual vmm_xactor::main() does not call super.main()");
               end
            end
         join_none

         // Wait to reset
         while (!this.reset_it) @(this.control_event);
         this.reset_it  = 0;
         this.n_threads_to_stop = -1;
         this.n_threads_stopped = 0;
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Reset"));
            this.log.end_msg();
         end
         this.is_stopped = 1;
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
         this.notify.reset(XACTOR_STOPPING);
         this.notify.indicate(XACTOR_IS_STOPPED);
         this.notify.indicate(XACTOR_STOPPED);
         this.notify.indicate(XACTOR_RESET);
         disable fork;
      end
   end
   join_none
endfunction: new


// //////////////////////////////////////////// 
// Function: get_name 
//    Returns the name of this transactor.
function string vmm_xactor::get_name();
   get_name = this.log.get_name();
endfunction:get_name


// //////////////////////////////////////////// 
// Function: get_instance 
//    Returns the instance name of this transactor.
function string vmm_xactor::get_instance();
   get_instance = this.log.get_instance();
endfunction: get_instance


// //////////////////////////////////////////// 
// Function: start_xactor 
// 
// Starts the execution threads in this transactor instance. The transactor can later
// be stopped. Any extension of this method must call the super.start_xactor() method.
// The base class indicates the XACTOR_STARTED and XACTOR_BUSY
// notifications, and resets the XACTOR_IDLE notification. 
// 
//|   
//|   class tb_env extends vmm_env;
//|      ...
//|      virtual task start();
//|         super.start();
//|         ...
//|         this.mac.start_xactor();
//|         ...
//|      endtask: start
//|      ...
//|   endclass: tb_env
function void vmm_xactor::start_xactor();
   this.start_it = 1;
   this.stop_it  = 0;
   -> this.control_event;
   this.notify.reset(XACTOR_STOPPING);
endfunction: start_xactor


// //////////////////////////////////////////// 
// Function: stop_xactor 
// 
// Stops the execution threads in this transactor instance. The transactor can later
// be restarted. Any extension of this method must call the super.stop_xactor() method.
// The transactor stops, when the <wait_if_stopped() or wait_if_stopped_or_empty>
// method is called. It is a call to these methods to define the granularity of stopping
// a transactor. 
// 
function void vmm_xactor::stop_xactor();
   this.start_it = 0;
   this.stop_it  = 1;
   -> this.control_event;
   this.notify.indicate(XACTOR_STOPPING);

   // Is it already stopped?
   if (this.is_stopped) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("Already stopped"));
         this.log.end_msg();
      end
      this.notify.indicate(XACTOR_STOPPED);
      return;
   end

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Stop requested"));
      this.log.end_msg();
   end
   this.check_all_threads_stopped();
endfunction: stop_xactor


// //////////////////////////////////////////// 
// Function: reset_xactor 
// 
// Resets the state, and terminates the execution threads in this transactor instance,
// according to the specified reset type (see Table A-8). The base class indicates the
// XACTOR_RESET and XACTOR_IDLE notifications, and resets
// the XACTOR_BUSY notification. 
// Reset Types 
// Enumerated Value Broadcasting Operation 
// SOFT_RST Clears the content of all channels, resets all ON_OFF notifications,
// and terminates all execution threads. However, maintains the current configuration,
// notification service, and random number generation state information. The transactor
// must be restarted. This reset type must be implemented. 
// PROTOCOL_RST Equivalent to a reset signaled through the physical interface.
// The information affected by this reset is user defined. 
// FIRM_RST Like SOFT_RST, but resets all notification service interface
// and random-number-generation state information. This reset type must be implemented.
// 
// HARD_RST Resets the transactor to the same state, found after construction.
// The registered callbacks are unregistered. 
// 
// To facilitate the implementation of this method, the actual values associated with
// these symbolic properties are of increasing magnitude (for example, <FIRM_RST
// is greater than SOFT_RST). Not all reset types may be implemented by all
// transactors. Any extension of this method must call super.reset_xactor(rst_type)
// first to terminate the main() method, reset the notifications, and reset
// the main thread seed according to the specified reset type. Calling the super.reset_xactor>
// method with a reset type of PROTOCOL_RST is functionally equivalent
// to SOFT_RST. 
// 
//|   
//|   function void
//|      mii_mac_layer::reset_xactor(reset_e typ = SOFT_RST);
//|      super.start_xactor(typ);
//|      ...
//|   endfunction: reset_xactor
function void vmm_xactor::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   this.start_it = 0;
   this.reset_it = 1;
   -> this.control_event;
   this.is_stopped = 1;

   // Reset notifier & RNG state on FIRM and above
   if (rst_typ == FIRM_RST ||
       rst_typ == HARD_RST) begin
      this.notify.reset(-1, vmm_notify::HARD);
      this.restore_rng_state();
   end
   else begin
      this.notify.reset(-1, vmm_notify::SOFT);
   end

   // Unregister all callbacks on HARD reset
   if (rst_typ == HARD_RST) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      this.callbacks.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      this.callbacks = '{};
`endif
   end
endfunction: reset_xactor


// //////////////////////////////////////////// 
// Function: save_rng_state 
// 
// This method saves, in local properties, the state of all random generators associated
// with this transactor instance. 
// 
function void vmm_xactor::save_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Saving RNG state information..."));
      this.log.end_msg();
   end

   if (!this.is_stopped) begin
      `vmm_warning(this.log, "save_rng_state() called while transactor is still running");
   end
   this.save_main_rng_state = 1;
endfunction: save_rng_state


// //////////////////////////////////////////// 
// Function: restore_rng_state 
// 
// This method restores, from local properties, the state of all random generators associated
// with this transactor instance. 
// 
function void vmm_xactor::restore_rng_state();
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      void'(this.log.text("Restoring RNG state information..."));
      this.log.end_msg();
   end

   if (!this.is_stopped) begin
      `vmm_warning(this.log, "restore_rng_state() called while transactor is still running");
   end
   this.restore_main_rng_state = 1;
endfunction: restore_rng_state


// //////////////////////////////////////////// 
// Function: psdisplay 
// 
// This method returns a human-readable description of the transactor. Each line is prefixed
// with the specified prefix. 
// 
//|   
//|   class xactor extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   program prog;
//|      xactor xact = new;
//|      ...
//|      initial begin
//|         ...
//|          $display("Printing variables of Transactor\n %s \n", 
//|            xact.psdisplay());
//|         ...
//|      end
//|   
//|   endprogram
function string vmm_xactor::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sTransactor %s (%s):", prefix,
            this.log.get_name(), this.log.get_instance());

   if (this.is_stopped) begin
      return {psdisplay, "\n", prefix, "Transactor is STOPPED"};
   end

   if (this.n_threads_stopped < this.n_threads_to_stop) begin
      return `vmm_sformatf("%s\n%sTransactor is STOPPING (%0d out of %0d threads stopped)",
                           psdisplay, prefix, this.n_threads_stopped,
                           this.n_threads_to_stop);
   end

   return {psdisplay, "\n", prefix, "Transactor is RUNNING"};
endfunction: psdisplay


function void vmm_xactor::xactor_status(string prefix = "");
   `vmm_note(this.log, this.psdisplay(prefix));
endfunction: xactor_status


// //////////////////////////////////////////// 
// Task: main
//  This task is forked off, whenever the start_xactor() method is called. 
// It is terminated, whenever the reset_xactor() method is called. The 
// functionality of a user-defined transactor must be implemented in this 
// method. Any additional subthreads must be started within this method, 
// not in the constructor. It can contain a blocking or non-blocking 
// implementation. 
//
// Any extension of this method must first fork a call to the super.main() method.
  
task vmm_xactor::main();
   this.main_running = 1;
endtask: main


function void vmm_xactor::check_all_threads_stopped();
   if (this.n_threads_to_stop > 0) begin
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text($psprintf("%0d out of %0d threads have now stopped",n_threads_stopped,this.n_threads_to_stop)));
         this.log.end_msg();
      end

      if (this.n_threads_stopped >= this.n_threads_to_stop) begin
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Stopped"));
            this.log.end_msg();
         end
         
         this.is_stopped = 1;
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
         this.notify.reset(XACTOR_STOPPING);
         this.notify.indicate(XACTOR_IS_STOPPED);
         this.notify.indicate(XACTOR_STOPPED);
      end
   end
endfunction


// //////////////////////////////////////////// 
// 
// Task: wait_if_stopped 
// 
// Blocks the thread execution, if the transactor is stopped through the stop_xactor()
// method. This method indicates the <XACTOR_STOPPED and XACTOR_IDLE
// notifications, and resets the XACTOR_BUSY notification. The tasks
// will return, once the transactor is restarted using the start_xactor> method, and
// the specified input channel is not empty. These methods do not block, if the transactor
// is not stopped and the specified input channel is not empty. 
// Calls to this method and the <wait_if_stopped_or_empty() methods
// define the granularity, by which the transactor can be stopped without violating the
// protocol. If a transaction can be suspended in the middle of its execution, then the
// wait_if_stopped() method should be called at every opportunity. If a transaction
// cannot be suspended, then the wait_if_stopped_or_empty> method should only be called
// after the current transaction is completed, before fetching the next transaction
// descriptor for the input channel. 
// If a transactor is implemented using more than one concurrently running thread that
// must be stopped, the total number of threads to be stopped must be specified in all invocations
// of this and the <wait_if_stopped_or_empty> method. 
// 
//|   
//|   protected virtual task main();
//|      super.main();
//|      forever begin
//|         transaction tr;
//|         this.wait_if_stopped_or_empty(this.in_chan);
//|         this.in_chan.activate(tr);
//|         ...
//|         this.wait_if_stopped();
//|         ...
//|      end
//|   endtask: main
task vmm_xactor::wait_if_stopped(int unsigned n_threads = 1);
   if (n_threads == 0) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
         void'(this.log.text("Number of threads to stop specified to vmm_xactor::wait_if_stopped() must be greater than 0"));
         this.log.end_msg();
      end
      n_threads = 1;
   end

   if (this.n_threads_to_stop <= 0) this.n_threads_to_stop = n_threads;
   else if (this.n_threads_to_stop != n_threads) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
         void'(this.log.text("All threads must specify the same number of threads to stop to vmm_xactor::wait_if_stopped() and  vmm_xactor::wait_if_stopped_or_empty()"));
         this.log.end_msg();
      end
      if (this.n_threads_to_stop < n_threads) this.n_threads_to_stop = n_threads;
   end

   if (this.stop_it) begin
      this.n_threads_stopped++;
      this.check_all_threads_stopped();

      while (this.stop_it) @(this.control_event);
      // Make sure these are done only once if
      // there are multiple stopped threads
      if (this.is_stopped) begin
         if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
            void'(this.log.text("Restarted"));
            this.log.end_msg();
         end
         this.is_stopped = 0;
         this.notify.indicate(XACTOR_STARTED);
         this.notify.reset(XACTOR_IS_STOPPED);
         this.notify.reset(XACTOR_IDLE);
         this.notify.indicate(XACTOR_BUSY);
      end
      this.n_threads_stopped--;
   end
endtask: wait_if_stopped


// //////////////////////////////////////////// 
// 
// Task: wait_if_stopped_or_empty 
// 
// Blocks the thread execution, if the transactor is stopped through the stop_xactor()
// method, or if the specified input channel is currently empty. This method indicates
// the <XACTOR_STOPPED and XACTOR_IDLE notifications,
// and resets the XACTOR_BUSY notification. The tasks will return, once
// the transactor is restarted using the start_xactor> method, and the specified input
// channel is not empty. These methods do not block, if the transactor is not stopped and
// the specified input channel is not empty. 
// Calls to this method and the <wait_if_stopped> methods define the
// granularity, by which the transactor can be stopped without violating the protocol.
// 
// If a transactor is implemented using more than one concurrently running thread that
// must be stopped, then the total number of threads to be stopped must be specified in all
// invocations of this and the <wait_if_stopped> method. 
// 
//|   
//|   protected virtual task main();
//|      super.main();
//|      fork
//|         forever begin
//|            transaction tr;
//|            this.wait_if_stopped_or_empty(this.in_chan, 2);
//|            this.in_chan.activate(tr);
//|            ...
//|            this.wait_if_stopped(2);
//|            ...
//|         end
//|   
//|         forever begin
//|            ...
//|            this.wait_if_stopped(2);
//|            ...
//|         end
//|      join_none
//|   endtask: main
task vmm_xactor::wait_if_stopped_or_empty(vmm_channel  chan,
                                          int unsigned n_threads = 1);
   if(chan == null) begin
     `vmm_error(this.log,"Passed null reference for channel to wait_if_stopped_or_empty");
     return;
   end

   this.wait_if_stopped(n_threads); 
   while (chan.level() == 0) begin
       vmm_data data;

       this.n_threads_stopped++;
       // If all other threads are blocked, indicate IDLE
       // because we are going to block on the channel
       if (this.n_threads_stopped >= this.n_threads_to_stop) begin
         this.notify.reset(XACTOR_BUSY);
         this.notify.indicate(XACTOR_IDLE);
       end

       if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
          void'(this.log.text($psprintf("%0d threads have now stopped or blocked",n_threads_stopped)));
          this.log.end_msg();
       end

       chan.peek(data);
       this.n_threads_stopped--;
       this.wait_if_stopped(n_threads);
  end

  this.notify.reset(XACTOR_IDLE);
  this.notify.indicate(XACTOR_BUSY);
endtask: wait_if_stopped_or_empty


// //////////////////////////////////////////// 
// Function: prepend_callback 
// 
// Callback methods are invoked in the order in which they were registered. 
// A warning is generated, if the same callback façade instance is registered more than
// once with the same transactor. A façade instance can be registered with more than one
// transactor. Callback façade instances can be unregistered and re-registered dynamically.
// 
// 
//|   
//|   program test;
//|   initial begin
//|      dut_env env = new;
//|      align_tx cb = new(...);
//|      env.build();
//|      foreach (env.mii[i]) begin
//|         env.mii[i].prepend_callback(cb);
//|      end
//|      env.run();
//|   end
//|   endprogram
function void vmm_xactor::prepend_callback(vmm_xactor_callbacks cb);
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
// Callback methods are invoked in the order in which they were registered. 
// A warning is generated, if the same callback façade instance is registered more than
// once with the same transactor. A façade instance can be registered with more than one
// transactor. Callback façade instances can be unregistered and re-registered dynamically.
// 
// 
function void vmm_xactor::append_callback(vmm_xactor_callbacks cb);
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
// Unregisters the specified callback façade instance, for this transactor instance.
// A warning is generated, if the specified façade instance is not currently registered
// with the transactor. Callback façade instances can later be re-registered with the
// same or another transactor. 
// 
function void vmm_xactor::unregister_callback(vmm_xactor_callbacks cb);
   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         // Unregister it
         this.callbacks.delete(i);
         return;
      end
   end

   `vmm_warning(this.log, "Callback was not registered");
endfunction: unregister_callback


// //////////////////////////////////////////// 
// Function: get_input_channels 
// 
// Returns the channels where this transactor is identified as the consumer using the
// <vmm_channel::set_consumer> method. 
// 
//|   
//|   class xactor extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   program prog;
//|      xactor xact = new;
//|      vmm_channel in_chans[$];
//|      ...
//|      initial begin
//|         ...
//|         xact.get_input_channels(in_chans);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_xactor::get_input_channels(ref vmm_channel chans[$]);
   chans = this.Xinput_chansX;
endfunction: get_input_channels


// //////////////////////////////////////////// 
// Function: get_output_channels 
// 
// Returns the channels where this transactor is identified as the producer, using the
// <vmm_channel::set_producer> method. 
// 
//|   
//|   class xactor extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   program prog;
//|      xactor xact = new;
//|      vmm_channel out_chans[$];
//|      ...
//|      initial begin
//|         ...
//|         xact.get_output_channels (out_chans);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_xactor::get_output_channels(ref vmm_channel chans[$]);
   chans = this.Xoutput_chansX;
endfunction: get_output_channels


// //////////////////////////////////////////// 
// Function: kill 
// 
// Prepares a transactor for deletion and reclamation by the garbage collector. 
// Removes this transactor as the producer of its output channels, and as the consumer
// of its input channels. De-registers all data stream scoreboards and callback extensions.
// 
// 
//|   
//|   class xactor extends vmm_xactor;
//|      ...
//|   endclass
//|   program prog;
//|      xactor xact = new;
//|      ...
//|      initial begin
//|         xact.kill();
//|         ...
//|      end
//|   endprogram
function void vmm_xactor::kill();
   vmm_channel ins[$] = this.Xinput_chansX;
   vmm_channel outs[$] = this.Xoutput_chansX;

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.Xinput_chansX.delete();
   this.Xoutput_chansX.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.Xinput_chansX = '{};
   this.Xoutput_chansX = '{};
`endif
   
   foreach(ins[i]) begin
      if (ins[i].get_consumer() == this) begin
         ins[i].set_consumer(null);
         if (ins[i].get_producer() == null) ins[i].kill();
      end
   end
      
   foreach(outs[i]) begin
      if (outs[i].get_producer() == this) begin
         outs[i].set_producer(null);
         if (outs[i].get_consumer() == null) outs[i].kill();
      end
   end
      
   foreach(this._vmm_available_xactor[i]) begin
     if (this._vmm_available_xactor[i] == this) begin
        this._vmm_available_xactor.delete(i);
        break;
     end
   end

   this.log.kill();
endfunction: kill




`ifdef VMM_SB_DS_IN_STDLIB
function void vmm_xactor::inp_vmm_sb_ds(vmm_data tr);
   vmm_sb_ds _temp_sb;
   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].is_in) begin
         if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
            _temp_sb.insert(tr);
      end
   end
endfunction: inp_vmm_sb_ds


function void vmm_xactor::exp_vmm_sb_ds(vmm_data tr);
   vmm_sb_ds _temp_sb;
   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].is_out) begin
         case (this._vmm_sb_ds[i].order)
           vmm_sb_ds::IN_ORDER:
           if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
              _temp_sb.expect_in_order(tr);

           vmm_sb_ds::WITH_LOSSES: begin
              vmm_data p;
              vmm_data losses[];
              if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
                 _temp_sb.expect_with_losses(tr, p, losses);
           end

           vmm_sb_ds::OUT_ORDER:
              if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
                 _temp_sb.expect_out_of_order(tr);

         endcase
      end
   end
endfunction: exp_vmm_sb_ds


function void vmm_xactor::register_vmm_sb_ds(vmm_sb_ds_base             sb,
                                             vmm_sb_ds::kind_e     kind,
                                             vmm_sb_ds::ordering_e order = vmm_sb_ds::IN_ORDER);
   vmm_sb_ds_registration ds;

   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         `vmm_warning(this.log, "Data stream scoreboard is already registered");
         return;
      end
   end

   if(sb == null) begin
     `vmm_error(this.log,"Trying to register null reference to register_vmm_sb_ds");
     return;
   end

   ds = new;
   ds.sb = sb;
   ds.is_in = (kind == vmm_sb_ds::INPUT ||
               kind == vmm_sb_ds::EITHER);
   ds.is_out = (kind == vmm_sb_ds::EXPECT ||
                kind == vmm_sb_ds::EITHER);
   ds.order = order;
   this._vmm_sb_ds.push_back(ds);
endfunction: register_vmm_sb_ds


function void vmm_xactor::unregister_vmm_sb_ds(vmm_sb_ds_base sb);
   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         this._vmm_sb_ds.delete(i);
         return;
      end
   end

   `vmm_error(this.log, "Data stream scoreboard is not registered");
endfunction: unregister_vmm_sb_ds
`endif


// //////////////////////////////////////////// 
// Function: do_psdisplay 
// 
// This method overrides the default implementation of the <psdisplay>
// method, created by the vmm_xactor shorthand macros. If defined, it will be used instead
// of the default implementation. 
// 
//|   
//|   class eth_frame_gen extends vmm_xactor;
//|      ...
//|      `vmm_xactor_member_begin(eth_frame_gen)
//|      ...
//|      `vmm_xactor_member_end(eth_frame_gen)
//|        virtual function string do_psdisplay(string prefix = "")
//|         $sformat(do_psdisplay,"%s Printing Ethernet frame \n
//|             generator members \n",prefix);
//|         ...
//|      endfunction
//|      ...
//|   endclass
function string vmm_xactor::do_psdisplay(string prefix = "");
   this.__vmm_done_user = 0;
   return "";
endfunction


// //////////////////////////////////////////// 
// Function: do_start_xactor 
// 
// Overrides the default implementation of the <start_xactor> method,
// created by the vmm_xactor shorthand macros. If defined, it is used instead of the default
// implementation. 
// 
//|   
//|   class xact1 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact2 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact extends vmm_xactor;
//|      xact1 xact1_inst;
//|      xact2 xact2_inst;
//|      ...
//|   `vmm_xactor_member_begin(xact)
//|      vmm_xactor_member_xactor(xact1_inst,DO_ALL)
//|      vmm_xactor_member_xactor(xact2_inst,DO_ALL)
//|   `vmm_xactor_member_end(xact)
//|      protected virtual function void do_start_xactor ();
//|        `ifdef XACT_2
//|           xact2_inst.start_xactor();
//|         `else
//|         xact1_inst.start_xactor();
//|         `endif
//|      ...
//|      endfunction
//|      ...
//|   endclass
function void vmm_xactor::do_start_xactor();
   this.__vmm_done_user = 0;
endfunction


// //////////////////////////////////////////// 
// Function: do_stop_xactor 
// 
// This method overrides the default implementation of the <stop_xactor>
// method, created by the vmm_xactor shorthand macros. If defined, it will be used instead
// of the default implementation. 
// 
//|   
//|   class xact1 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact2 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact extends vmm_xactor;
//|      xact1 xact1_inst;
//|      xact2 xact2_inst;
//|      ...
//|   `vmm_xactor_member_begin(xact)
//|      vmm_xactor_member_xactor(xact1_inst,DO_ALL)
//|      vmm_xactor_member_xactor(xact2_inst,DO_ALL)
//|   `vmm_xactor_member_end(xact)
//|      protected virtual function void do_stop_xactor ();
//|        `ifdef XACT_2
//|           xact2_inst.stop_xactor();
//|         `else
//|         xact1_inst.stop_xactor();
//|         `endif
//|         ...
//|      endfunction
//|      ...
//|   endclass
function void vmm_xactor::do_stop_xactor();
   this.__vmm_done_user = 0;
endfunction


// //////////////////////////////////////////// 
// Function: do_reset_xactor 
// 
// Overrides the default implementation of the <reset_xactor> method
// created by the vmm_xactor shorthand macros. If defined, it is used instead of the default
// implementation. 
// 
//|   
//|   class xact1 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact2 extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   class xact extends vmm_xactor;
//|      xact1 xact1_inst;
//|      xact2 xact2_inst;
//|      ...
//|   `vmm_xactor_member_begin(xact)
//|      vmm_xactor_member_xactor(xact1_inst,DO_ALL)
//|      vmm_xactor_member_xactor(xact2_inst,DO_ALL)
//|   `vmm_xactor_member_end(xact)
//|      protected virtual function void do_reset_xactor ();
//|        `ifdef XACT_2
//|           xact2_inst.reset_xactor();
//|        `else
//|         xact1_inst.reset_xactor();
//|        `endif
//|        ...
//|      endfunction
//|      ...
//|   endclass
function void vmm_xactor::do_reset_xactor(vmm_xactor::reset_e rst_typ);
   this.__vmm_done_user = 0;
endfunction


function void vmm_xactor::do_kill_xactor();
   this.__vmm_done_user = 0;
endfunction


// //////////////////////////////////////////// 
// Class: vmm_xactor_iter
// 
// This class can iterate over all known vmm_xactor instances, based on the names 
// and instance names, regardless of their location in the class hierarchy. VMM 
// adds this class to traverse list a registered transactors that match a regular 
// expression. 
// 
// This feature is useful to register specific transactor callbacks, 
// connect specific transactors to a scoreboard object, and re-allocate transactor, 
// by killing its channels and reassigning some new ones.
//
// (start code)
//   class driver_typed #(type T = vmm_data) extends vmm_xactor;
//     function new(string instance);
//       super.new("driver", instance);
//     endfunction
//     virtual protected task main();
//       vmm_channel chans[$];
//       super.main();
//       get_input_channels(chans);
//       foreach (chans[i]) begin
//         vmm_channel_typed #(T) chan;
//         $cast(chan, chans[i]);
//         start_drive(chan, i);
//       end
//   endtask
//
//   virtual task start_drive(vmm_channel_typed #(T) chan);
//     T tr;
//     fork
//       forever begin
//         chan.get(tr);
//         `vmm_note(log, tr.psdisplay(¡ÈExecuting.."));
//         wait_if_stopped();
//       end
//     join_none
//   endtask
// endclass
//
// (end code)

//////////////////////////////////////////////
// Function: vmm_xactor_iter::new
//
//    Creates a new transactor iterato,r and initializes it using the specified name 
// and instance name. If the specified name or instance name is enclosed between 
// /./ characters, they are interpreted as regular expressions. 
// Otherwise, they are interpreted as the full name or instance name to match.
//    The <first> is implicitly called.  
// So, once created, the first transactor matching the specified name and instance
// name patterns is available, using the <xactor()> method.  
// The subsequent transactors can be iterated on, one at a time,
// using the <next> method.
//
//|   vmm_xactor_iter iter = new("/AHB/");
//|   while (iter.xactor() != null) begin
//|      ahb_master ahb;
//|      if ($cast(ahb, iter.xactor()) begin
//|         ...
//|      end
//|      iter.next();
//|   end
//////////////////////////////////////////////

function vmm_xactor_iter::new(string  name = "",
                              string  inst = "");
   if (name == "") this.name = ".";
   else begin
      // Remove "/" surrounding the pattern, if any
      if (`vmm_str_match(name, "^/(.*)/$")) name = `vmm_str_backref(name, 0);
      this.name = name;
   end

   if (inst == "") this.inst = ".";
   else begin
      // Remove "/" surrounding the pattern, if any
      if (`vmm_str_match(inst, "^/(.*)/$")) inst = `vmm_str_backref(inst, 0);
      this.inst = inst;
   end

   void'(this.first());
endfunction: new


function void vmm_xactor_iter::move_iterator();
   string xa_name;
   string xa_inst;
`ifdef NO_STATIC_METHODS
   int n;

   if (_vmm_xactor == null) begin
      _vmm_xactor = new("vmm_xactor_iter::_vmm_xactor", "static");

      // Make sure it is the first one on the list of known transactors
      if (_vmm_xactor._vmm_available_xactor[0] == null) begin
         void'(_vmm_xactor._vmm_available_xactor.pop_back());
         _vmm_xactor._vmm_available_xactor[0] = _vmm_xactor;
      end
   end
   n = _vmm_xactor._vmm_available_xactor.size();
`else
   int n = vmm_xactor::_vmm_available_xactor.size();
`endif

   if (this.idx >= n || n <= 1) return;

   for (int x = this.idx+1; x < n; x++) begin
`ifdef NO_STATIC_METHODS
      xa_name = _vmm_xactor._vmm_available_xactor[x].log.get_name();
      xa_inst = _vmm_xactor._vmm_available_xactor[x].log.get_instance();
`else
      xa_name = vmm_xactor::_vmm_available_xactor[x].log.get_name();
      xa_inst = vmm_xactor::_vmm_available_xactor[x].log.get_instance();
`endif

      if (`vmm_str_match(xa_name, this.name) &&
          `vmm_str_match(xa_inst, this.inst)) begin
         this.idx = x;
         return;
      end
   end
   this.idx = 0;
endfunction


function vmm_xactor vmm_xactor_iter::xactor();
`ifdef NO_STATIC_METHODS
   if (_vmm_xactor == null) begin
      _vmm_xactor = new("vmm_xactor_iter::_vmm_xactor", "static");
   end
`endif

   if (this.idx <= 0 ||
`ifdef NO_STATIC_METHODS
       this.idx >= _vmm_xactor._vmm_available_xactor.size())
`else
       this.idx >= vmm_xactor::_vmm_available_xactor.size())
`endif
     return null;

`ifdef NO_STATIC_METHODS
   return _vmm_xactor._vmm_available_xactor[this.idx];
`else
   return vmm_xactor::_vmm_available_xactor[this.idx];
`endif
endfunction


//////////////////////////////////////////////
// Function: vmm_xactor_iter::first
//
//    Resets the iterator to the first transactor matching the name and instance name 
// patterns specified, when the iterator was created using the <new> 
// method and return a reference to it, if found.
//    Returns NULL, if no transactors match.
//    The order in which transactors are iterated on is unspecified.
//
//////////////////////////////////////////////
function vmm_xactor vmm_xactor_iter::first();
   this.idx = 0;
   this.move_iterator();
   return this.xactor();
endfunction  

//////////////////////////////////////////////
// Function: vmm_xactor_iter::next
//
//    Moved the iterator to the next transactor, matching the name and instance 
// name patterns specified, when the iterator was created using the <new> method 
// and return a reference to it, if found.
//    Returns NULL, if no transactors match.
//    The order in which transactors are iterated on is unspecified.
//
//////////////////////////////////////////////
function vmm_xactor vmm_xactor_iter::next();
   this.move_iterator();
   return this.xactor();
endfunction  
