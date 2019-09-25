// //////////////////////////////////////////// 
//
// Class:  vmm_scheduler
//
// Channels are point-to-point transaction descriptor transfer mechanisms. 
// If multiple sources are adding descriptors to a single channel, then the 
// descriptors are interleaved with the descriptors from the other sources, 
// in a fair but uncontrollable way. If a multi-point-to-point mechanism is 
// required to follow a specific scheduling algorithm, a vmm_scheduler component 
// can be used to identify which source stream should next be forwarded to the 
// output stream.
//
// This class is based on the <vmm_xactor> class.
    

// //////////////////////////////////////////// 
// Function: new 
// 
// Creates a new instance of a channel scheduler object with the specified name, instance
// name, destination channel, and optional instance identifier. 
// 
//|   
//|   class atm_subenv extends vmm_subenv;
//|      atm_scheduler scheduler;
//|      atm_cell_channel chan_2;
//|      ...
//|      task sub_build();
//|         chan_2  = new("chan_2", "gen");
//|         scheduler = new("schedular","subenv",chan_2,1);
//|         ...
//|      endtask
//|   endclass
function vmm_scheduler::new(string       name,
                            string       inst,
                            vmm_channel  destination,
                            int          instance_id = -1
                            `VMM12_XACTOR_NEW_EXTERN_ARGS `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new(name, inst, instance_id `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL);
   
   this.out_chan = destination;
   if (out_chan)
      this.log.is_above(this.out_chan.log);

   this.randomized_sched = new;

   this.instance_id = instance_id;
   this.election_count = 0;
endfunction : new


function string vmm_scheduler::psdisplay(string prefix = "");
   psdisplay = super.psdisplay(prefix);
   $sformat(psdisplay, "%s\n%sOutChan: %s(%s) [level=%0d of %0d]",
            psdisplay, prefix, this.out_chan.log.get_name(),
            this.out_chan.log.get_instance(), this.out_chan.level(),
            this.out_chan.full_level());
   foreach (this.sources[i]) begin
      $sformat(psdisplay, "%s\n%sInChan[%0d/%s]: %s(%s) [level=%0d of %0d]",
               psdisplay, prefix, i, (this.is_on[i]) ? "ON " : "OFF",
               this.sources[i].log.get_name(),
               this.sources[i].log.get_instance(), this.sources[i].level(),
               this.sources[i].full_level());
   end
   return psdisplay;
endfunction


// //////////////////////////////////////////// 
// Function: new_source 
// 
// Adds the specified channel instance, as a new input channel to the scheduler. This method
// returns an identifier for the input channel that must be used to modify the configuration
// of the input channel or -1, if an error occurred. 
// Any user extension of this method must call the super.new_source() method. 
// 
//|   
//|   int int_id;
//|   atm_cell_channel sources[$];
//|   function build();
//|      ...
//|      sources.push_back(chan_2);
//|      sources.push_back(chan_3);
//|      int_id = scheduler.new_source(chan_1);
//|      int_id = scheduler.new_source(chan_2);
//|      ...
//|   endfunction
function int vmm_scheduler::new_source(vmm_channel channel);
   if (channel == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         void'(this.log.text("Attempting to add a NULL source channel"));
         this.log.end_msg();
      end
      return -1;
   end
   
   new_source = this.sources.size();
   
   this.sources.push_back(channel);
   this.is_on.push_back(1);
   if (channel.level() > 0) begin
      -> this.next_cycle;
   end

   // Watch for new additions to the newly added source
   // to potentially trigger new scheduling cycles
   fork 
      while (1) begin
         // The input channel may have been filled
         // before the forked thread has had a chance
         // to wait on the PUT indication
         if (channel.level() > 0) begin
            -> this.next_cycle;
         end
         channel.notify.wait_for(vmm_channel::PUT);
         -> this.next_cycle;
      end
   join_none 
  
endfunction : new_source


function void vmm_scheduler::set_output(vmm_channel destination);
   if (out_chan == null) begin
      out_chan = destination;
      this.log.is_above(this.out_chan.log);
   end else begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         void'(this.log.text("Destination channel already set, ignoring set_input call"));
         this.log.end_msg();
      end
   end
endfunction : set_output


// //////////////////////////////////////////// 
// Function: sched_from_input 
// 
// By default, scheduling from an input channel is on. When scheduling is turned off, the
// input channel is not flushed and the scheduling of new transaction descriptors from
// that source channel is inhibited. The scheduling of descriptors from that source channel
// is resumed, as soon as scheduling is turned on. 
// Any user extension of this method should call the super.sched_off() method. 
// 
task vmm_scheduler::sched_from_input(int channel_id,
                                     int on_off);
   if (channel_id < 0 || channel_id >= this.sources.size()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         string msg;
         $sformat(msg, "Invalid source channel ID specified in vmm_scheduler::sched_from_input(): %0d", channel_id);
         void'(this.log.text(msg));
         this.log.end_msg();
      end
      return;
   end

   this.is_on[channel_id] = on_off;

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      string msg;
      $sformat(msg, "Scheduling from channel #%0d turned %s", channel_id,
              (on_off) ? "ON" : "OFF");
      void'(this.log.text(msg));
      this.log.end_msg();
   end

   if (on_off && this.sources[channel_id].level() > 0) begin
      -> this.next_cycle;
   end
endtask : sched_from_input


// //////////////////////////////////////////// 
// 
// Task: schedule 
// 
// Overloading this method allows the creation of scheduling components with different
// rules. It is invoked for each scheduling cycle. The transaction descriptor returned
// by this method in the obj argument is added to the output channel. If this method returns
// null, no descriptor is added for this scheduling cycle. The input channels provided
// in the sources argument are all the currently non-empty ON input channels. Their corresponding
// input identifier is found in the input_ids argument. 
// New scheduling cycles are attempted, whenever the output channel is not full. If no
// transaction descriptor is scheduled from any of the currently non-empty source channels,
// then the next scheduling cycle will be delayed until an additional ON source channel
// becomes non-empty. Lock-up occurs, if there are no empty input channels and no OFF channels.
// 
// The default implementation of this method randomizes the instance found in the randomized_sched
// property. 
// 
//|   
//|   vmm_data  data_obj;
//|   int unsigned input_ids[$];
//|   ... 
//|   task start();
//|      ...
//|      #1;
//|      scheduler.start_xactor();
//|      input_ids = {0,1};
//|      scheduler.schedule(data_obj,sources,input_ids);
//|      ...
//|   endtask
//|   ...
task vmm_scheduler::schedule(output vmm_data     obj,
                             input  vmm_channel  sources[$],
                             input  int unsigned input_ids[$]);
   int     id;
   
   this.randomized_sched.instance_id = this.instance_id;
   this.randomized_sched.election_id = this.election_count++;
   this.randomized_sched.n_sources   = sources.size();
   this.randomized_sched.sources     = sources;
   this.randomized_sched.ids         = input_ids;

   // Round-robin scheduler  
   this.randomized_sched.next_idx = 0;
   if (this.randomized_sched.id_history.size() > 0) begin
      int last_id;
      // Find the next ID that follows (numerically) the last one
      // that was picked or use the first ID in the list of IDs.
      // Note: IDs will be stored in increasing numerical values.
      last_id = this.randomized_sched.id_history[$];
      foreach (input_ids[i]) begin
         if (input_ids[i] > last_id) begin
            this.randomized_sched.next_idx = i;
            break;
         end
      end
   end

   obj = null;
   if (!this.randomized_sched.randomize()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Unable to randomize vmm_scheduler::randomized_sched"));
         this.log.end_msg();
      end
      return;
   end
   if (this.randomized_sched.source_idx < 0) return;

   if (this.randomized_sched.source_idx >= input_ids.size()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::randomized_sched randomized to an invalid choice"));
         this.log.end_msg();
      end
      return;
   end
   
   id = input_ids[this.randomized_sched.source_idx];

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
      string msg;
      $sformat(msg, "Scheduled data from source #%0d, offset %0d",
              id, this.randomized_sched.obj_offset);
      void'(this.log.text(msg));
      this.log.end_msg();
   end

   begin
      vmm_channel src = this.sources[id]; 
      if (src == null || src.level() == 0 ||
          src.level() <= this.randomized_sched.obj_offset) begin
         if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
            void'(this.log.text("vmm_scheduler::randomized_sched randomized to an invalid source"));
            this.log.end_msg();
         end
         return;
      end
      this.get_object(obj, src, id, this.randomized_sched.obj_offset);
   end

   this.randomized_sched.id_history.push_back(id);
   this.randomized_sched.obj_history.push_back(obj);
   if (this.randomized_sched.id_history.size() > 10) begin
      void'(this.randomized_sched.id_history.pop_front());
      void'(this.randomized_sched.obj_history.pop_front());
   end
endtask : schedule


// //////////////////////////////////////////// 
// 
// Task: get_object 
// 
//|    virtual protected task get_object(
//|                           output vmm_data obj,
//|                           input vmm_channel source,
//|                           input int unsigned input_id,
//|                           input int offset);
// 
// This method is invoked by the default implementation of the <schedule>
// method to extract the next scheduled transaction descriptor from the specified input
// channel, at the specified offset within the channel. Overloading this method allows
// access to or replacement of the descriptor that is about to be scheduled. User-defined
// extensions can be used to introduce errors by modifying the object, interfere with
// the scheduling algorithm by substituting a different object, or recording of the schedule
// into a functional coverage model. 
// Any object that is returned by this method, through the obj argument, must be either
// internally created or physically removed from the input source using the <vmm_channel::get()
// method. If a reference to the object remains in the input channel (for example, by using
// the vmm_channel::peek() or vmm_channel::activate> method), then it is liable to
// be scheduled more than once, as the mere presence of an instance in any of the input channel
// makes it available to the scheduler. 
// 
//|   
//|   vmm_data  data_obj;
//|   int unsigned input_ids[$];
//|   ... 
//|   task start();
//|      ...
//|      #1;
//|      scheduler.start_xactor();
//|      input_ids = {0,1};
//|      scheduler.schedule(data_obj,sources,input_ids);
//|      scheduler.get_object(data_obj,chan_2,1,0);
//|      ... 
//|   endtask
task vmm_scheduler::get_object(output vmm_data     obj,
                               input  vmm_channel  source,
                               input  int unsigned input_id,
                               input  int          offset);
   obj = null;

   if (source == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::get_object called with invalid source"));
         this.log.end_msg();
      end
      return;
   end
   
   if (offset >= source.level()) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("vmm_scheduler::get_object called with invalid offset"));
         this.log.end_msg();
      end
      return;
   end
   
   source.get( obj, offset);
endtask : get_object


// //////////////////////////////////////////// 
// Function: start_xactor 
// 
// The scheduler can be stopped. Any extension of this method must call super.start_xactor().
// 
// 
//|   
//|   class atm_env extends vmm_env;
//|      ...
//|      task start();
//|         scheduler.start_xactor();
//|         ... 
//|      endtask
//|      ...
//|   endclass
function void vmm_scheduler::start_xactor();
   super.start_xactor();
   // This MAY cause a new scheduling cycle
   if (out_chan == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Scheduler started, but destination chnnel is yet not set"));
         this.log.end_msg();
      end
      return;
   end

   -> this.next_cycle;
endfunction : start_xactor


// //////////////////////////////////////////// 
// Function: stop_xactor 
// 
// The scheduler can be restarted. Any extension of this method must the call super.stop_xactor()
// method. 
// 
//|   
//|   class atm_env extends vmm_env;
//|      ... 
//|      task stop();
//|         scheduler.stop_xactor();
//|         ...
//|      endtask
//|      ...
//|   endclass
function void vmm_scheduler::stop_xactor();
   super.stop_xactor();
endfunction : stop_xactor


// //////////////////////////////////////////// 
// Function: reset_xactor 
// 
// The output channel and all input channels are flushed. If a HARD_RST reset type is specified,
// then the scheduler election factory instance in the randomized_sched property is
// replaced with a new default instance. 
// 
//|   
//|   class atm_env extends vmm_env;
//|      ...
//|      task reset_dut();
//|         scheduler.reset_xactor();
//|         ...
//|      endtask
//|      ... 
//|   endclass
function void vmm_scheduler::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
   super.reset_xactor(rst_typ);
   
   this.out_chan.flush();
   foreach (sources[i]) begin
      this.sources[i].flush();
   end

   this.instance_id = instance_id;
   this.election_count = 0;

   if (rst_typ == HARD_RST ) begin
      this.randomized_sched = new;
   end
endfunction


task vmm_scheduler::main();
   fork
      super.main();
      this.schedule_cycle();
   join_none
endtask


task vmm_scheduler::schedule_cycle();
   vmm_data          data;
   vmm_channel       srcs[$];
   int unsigned      ids[$];
   
   while (1) begin
`ifdef VCS2006_06
      // Work-around for NYI feature in VCS2006.06
      // but IEEE 1800-2009 compliant
      srcs.delete();
      ids.delete();
`else
      // Works in VCS2008.03 or later
      // IEEE 1800-2005 compliant
      srcs = '{};
      ids = '{};
`endif

      super.wait_if_stopped();

      // Identify all non-empty, active sources
      foreach (this.sources[i]) begin
         if (this.is_on[i] && this.sources[i] != null &&
             this.sources[i].level() > 0) begin
            srcs.push_back(this.sources[i]);
            ids.push_back(i);
         end
      end
      if (srcs.size() == 0) data = null;
      else this.schedule(data, srcs, ids);

      if (data == null) begin
         // Delay the next scheduling cycle until
         // A new channel is added, new data is put into
         // a channel, a channel is turned on or the scheduler
         // is restarted
         `vmm_trace(this.log, "Waiting for next scheduling cycle...");
         @ ( this.next_cycle);
         continue;
      end
      this.out_chan.put(data);
   end
endtask
   
