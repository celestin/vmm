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
// Class: vmm_channel
//
// This class implements a generic transaction-level interface mechanism. Offset values, 
// either accepted as arguments or returned values, are always interpreted the same way. 
// A value of 0 indicates the head of the channel (first transaction descriptor added). 
// A value of 1 indicates the tail of the channel (last transaction descriptor added). 
//
// Positive offsets are interpreted from the head of the channel. Negative offsets are 
// interpreted from the tail of the channel. For example, an offset value of 2 indicates 
// the transaction descriptor just before the last transaction descriptor in the channel. 
// It is illegal to specify a non-zero offset that does not correspond to a transaction 
// descriptor, which is already in the channel. 
//
// The channel includes an active slot 
// that can be used to create more complex transactor interfaces. The active slot counts 
// toward the number of transaction descriptors currently in the channel, for 
// control-flow purposes, but cannot be accessed nor specified through an offset specification.
  
// Function: new 
// 
// If the fill_as_bytes argument is TRUE (non-zero), then the full and empty levels and
// the fill level of the channel are interpreted as the number of bytes in the channel, as
// computed by the sum of <vmm_data::byte_size> of all transaction descriptors in the
// channel and not the number of objects in the channel. 
// If the value is FALSE (zero), the full and empty levels, and the fill level of the channel
// are interpreted as the number of transaction descriptors in the channel. 
// It is illegal to configure a channel with a full level, lower than the empty level. The
// parent argument specifies the type of parent class which instantiates this channel.
// 
// 
function vmm_channel::new(string       name,
                          string       inst,
                          int unsigned full=1,
                          int unsigned empty=0,
                          bit          fill_as_bytes=1'b0
						  `VMM_CHANNEL_BASE_NEW_EXTERN_ARGS);
`ifdef VMM_CHANNEL_BASE_NEW_CALL
   super.new(`VMM_CHANNEL_BASE_NEW_CALL);
`endif

  if (this.shared_log == null) begin
     this.one_log = _vmm_opts.get_bit("channel_shared_log",
                                      "All VMM channels share the same vmm_log instance");
     this.shared_log = new("VMM Channel", "[shared]");
  end

   if (this.one_log) this.log = shared_log;
`ifdef VMM_12_UNDERPIN_VMM_CHANNEL
   else this.log = new(name, this.get_object_hiername());
   `vmm_unit_config_boolean(pull_mode_on, "enable pull mode for channels and generators", 0, DO_ALL)
   if (pull_mode_on) begin
      set_mode(PULL_MODE);
   end
`else
   else this.log = new(name, inst);
`endif //VMM_12_UNDERPIN_VMM_CHANNEL

   this.shared_log = this.log;

`ifdef VMM_TR_RECORD
   this.top_stream = vmm_tr_record::open_stream(this.log.get_instance(), "Channel", vmm_debug::TRACE_SEV);
   this.sub_stream = vmm_tr_record::open_sub_stream(this.top_stream, "sub", vmm_debug::DEBUG_SEV);
`endif //VMM_TR_RECORD

   this.notify = new(this.log);
   `ifdef VMM_12_UNDERPIN_VMM_CHANNEL
   `ifdef VMM_12_UNDERPIN_VMM_NOTIFY
   `VMM_OBJECT_SET_PARENT(this.notify, this)
   `endif //VMM_12_UNDERPIN_VMM_NOTIFY
   `endif //VMM_12_UNDERPIN_VMM_CHANNEL

   void'(this.notify.configure(FULL,  vmm_notify::ON_OFF));
   void'(this.notify.configure(EMPTY, vmm_notify::ON_OFF));
   void'(this.notify.configure(PUT));
   void'(this.notify.configure(GOT));
   void'(this.notify.configure(PEEKED));
   void'(this.notify.configure(ACTIVATED));
   void'(this.notify.configure(ACT_STARTED));
   void'(this.notify.configure(ACT_COMPLETED));
   void'(this.notify.configure(ACT_REMOVED));
   void'(this.notify.configure(LOCKED));
   void'(this.notify.configure(UNLOCKED));
   void'(this.notify.configure(GRABBED));
   void'(this.notify.configure(UNGRABBED));
   void'(this.notify.configure(RECORDING, vmm_notify::ON_OFF));
   void'(this.notify.configure(PLAYBACK, vmm_notify::ON_OFF));
   void'(this.notify.configure(PLAYBACK_DONE, vmm_notify::ON_OFF));

   if (full <= 0) full = 1;
   if (empty < 0 || empty > full) empty = full;

   this.full = full;
   this.empty = empty;
   this.is_sunk  = 0;

   this.active = null;
   this.active_status = INACTIVE;
   this.tee_on = 0;
   this.downstream = null;
   this.locks  = 2'b00;

   this.full_chan = 0;
   this.notify.indicate(EMPTY);

   this.iterator = 0;
   this.is_put = 0;
   this.is_playback = 0;
   this.record_fp = -1;

   //
   // Thread to manage connection requests
   //
   fork: connection_requests
      while (1)
      begin : new_while_loop
         vmm_data data = null;

         // Broken connection?
         if (this.downstream != null)
         begin
            if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV))
            begin
               string txt;
               txt = {"Channel connection established: ",
                      this.log.get_name(),
                      "(", this.log.get_instance(), ") -> ",
                      this.downstream.log.get_name(),
                      "(", this.downstream.log.get_instance(), ")"};

               void'(this.log.text(txt));
               this.log.end_msg();
            end // if debug level

            // Fork the data mover thread
            fork
               while (1)
               begin : inner_while_loop
                  // Simple blocking interface
                  data = null;
                  this.peek(data);
                  this.downstream.put(data);
                  if (this.data.size() > 0 && this.data[0] == data) this.get(data);
               end // inner_while_loop
            join_none
         end // if downstream != null

         // Wait for new connection requests
         @this.new_connection;

         // Stop the data mover thread
         disable fork;

         // Remove any datum that was forwarded
         // to the downstream channel but not removed
         // from this channel because of the blocking
         // model. Otherwise, the same datum will be
         // obtained from this channel twice.
         if (data != null) this.get(data);
     end // while (1)
   join_none // connection_requests
endfunction : new


// //////////////////////////////////////////// 
// Function: reconfigure 
// 
// If not negative, this method reconfigures the full or empty levels of the channel to
// the specified levels . Reconfiguration may cause threads, which are currently blocked
// on a <put> call to unblock. If the fill_as_bytes argument is specified
// as 1b1 or 1b0, then the interpretation of the fill level of the channel is modified
// accordingly. Any other value, leaves the interpretation of the fill level unchanged.
// 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      transaction_channel in_chan;
//|      ...
//|      function new(transaction_channel in_chan = null);
//|         ...
//|         if (in_chan == null)
//|           in_chan = new(...);
//|         in_chan.reconfigure(1);
//|         this.in_chan = in_chan;
//|      endfunction: new
//|      ...
//|   endclass: consumer
function void vmm_channel::reconfigure(int   full=-1,
                                       int   empty=-1,
                                       logic fill_as_bytes=1'bx);
   if (full < 0) full = this.full;
   if (full == 0) full = 1;
   if (empty < 0) empty = this.empty;

   if (full < empty)
   begin
      `vmm_error(this.log, "Cannot reconfigure channel with FULL < EMPTY");
      return;
   end

   this.full = full;
   this.empty = empty;

   if (this.level() >= this.full)
   begin
      this.full_chan = 1;
      this.notify.indicate(FULL);
      this.notify.reset(EMPTY);
   end
   else if (this.level() <= this.empty)
   begin
      this.full_chan = 0;
      -> this.item_taken;
      this.notify.indicate(EMPTY);
      this.notify.reset(FULL);
   end
   else
   begin
      this.full_chan = 0;
      -> this.item_taken;
      this.notify.reset(EMPTY);
      this.notify.reset(FULL);
   end
endfunction: reconfigure


// //////////////////////////////////////////// 
// Function: full_level 
// 
// 
// 
function int unsigned vmm_channel::full_level();
   full_level = this.full;
endfunction: full_level


// //////////////////////////////////////////// 
// Function: empty_level 
// 
function int unsigned vmm_channel::empty_level();
   empty_level = this.empty;
endfunction: empty_level


// //////////////////////////////////////////// 
// Function: level 
// 
// The interpretation of the fill level depends on the configuration of the channel instance.
// 
// 
function int unsigned vmm_channel::level();
   level = this.data.size() + ((this.active == null) ? 0 : 1);
endfunction: level


// //////////////////////////////////////////// 
// Function: size 
// 
// Returns the number of transaction descriptors, which are currently in the channel,
// including the active slot, regardless of the interpretation of the fill level. 
// 
function int unsigned vmm_channel::size();
   size = this.data.size() + ((this.active == null) ? 0 : 1);
endfunction : size


// //////////////////////////////////////////// 
// Function: is_full 
// 
// Returns TRUE (that is, non-zero), if the fill level is greater than or equal to the currently
// configured full level. Otherwise, returns FALSE. 
// 
function bit vmm_channel::is_full();
   is_full = full_chan;
endfunction : is_full


// //////////////////////////////////////////// 
// Function: flush 
// 
// Flushing unblocks any thread, which is currently blocked in the <put>
// method. This method causes the FULL notification to be reset, or the EMPTY notification
// to be indicated. Flushing a channel unlocks all sources and consumers. 
// 
function void vmm_channel::flush();
   vmm_data obj;
   if (this.downstream != null)
      this.downstream.flush();

`ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.data.delete();
   this.tee_data.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.data = {};
   this.tee_data = {};
`endif //ifdef VCS2006_06
   full_chan = 0;
   this.active = null;
   this.active_status = INACTIVE ;
   -> this.item_taken;
   this.notify.reset(FULL);
   this.notify.indicate(EMPTY);
endfunction: flush

`ifndef VMM_GRAB_DISABLED
function void vmm_channel::reset_grabbers();
 `ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.grab_owners.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.grab_owners = {};
`endif //ifdef VCS2006_06
endfunction: reset_grabbers
`endif //ifndef VMM_GRAB_DISABLED


// //////////////////////////////////////////// 
// Function: sink 
// 
// No transaction descriptors will accumulate in the channel, while it is sunk. Any thread
// attempting to obtain a transaction descriptor from the channel will be blocked, until
// the flow through the channel is restored using the <flow> method. This
// method causes the FULL notification to be reset, or the EMPTY notification to be indicated.
// 
// 
function void vmm_channel::sink();
   this.flush();
   this.is_sunk = 1;
endfunction: sink


// //////////////////////////////////////////// 
// Function: flow 
// 
function void vmm_channel::flow();
   this.is_sunk = 0;
endfunction: flow


function void vmm_channel::reset();
   this.flush();
`ifndef VMM_GRAB_DISABLED
   this.reset_grabbers();
`endif
endfunction: reset


// //////////////////////////////////////////// 
// Function: lock 
// 
// The side that is to be locked or unlocked is specified using the sum of the symbolic values,
// as shown in Table A-2. 
// Although the source and sink contain same control-flow effect, locking a source does
// not indicate the FULL notification, nor does locking the sink indicate the EMPTY notification.
// 
// Channel Endpoint Identifiers 
// Symbolic Property Channel Endpoint 
// <SOURCE The producer side, i.e., any thread calling the put>
// method 
// <SINK The consumer side, i.e., any thread calling the get>
// method 
// 
// 
function void vmm_channel::lock(bit [1:0] who);
   this.locks |= who;
   this.notify.indicate(LOCKED);
endfunction: lock


// //////////////////////////////////////////// 
// Function: unlock 
// 
// The side that is to be locked or unlocked is specified using the sum of the symbolic values,
// as shown in Table A-2. 
// Although the source and sink contain the same control-flow effect, locking a source
// does not indicate the FULL notification, nor does locking the sink indicate the EMPTY
// notification. 
// 
function void vmm_channel::unlock(bit [1:0] who);
   this.locks &= ~who;
   this.notify.indicate(UNLOCKED);
   // May cause a consumer or producer to unblock
   -> this.item_taken;
   -> this.item_added;
endfunction: unlock


// //////////////////////////////////////////// 
// Function: is_locked 
// 
// Returns TRUE (non-zero), if any of the specified sides is locked. If both sides are specified,
// and if any side is locked, then returns TRUE. 
// 
//|   
//|   while (chan.is_locked(SOURCE
//|        SINK)) 
//|      begin
//|         chan.notify.wait_for(UNLOCKED);
//|      end
function bit vmm_channel::is_locked(bit [1:0] who);
   is_locked = (this.locks & who) ? 1 : 0;
endfunction: is_locked


`ifndef VMM_GRAB_DISABLED
function bit vmm_channel::check_grab_owners(`VMM_SCENARIO grabber);
   `VMM_SCENARIO current_parent;

   current_parent = grabber;

   while (current_parent != null) begin
      if (this.grab_owners[0] == current_parent) begin
         return 1;
      end
      current_parent = current_parent.get_parent_scenario();
   end
   return 0;
endfunction: check_grab_owners


function bit vmm_channel::check_all_grab_owners(`VMM_SCENARIO grabber);
   foreach (this.grab_owners[i]) begin
      if (grabber == this.grab_owners[i]) return 1;
   end
   return 0;
endfunction: check_all_grab_owners
`endif //ifndef VMM_GRAB_DISABLED


// //////////////////////////////////////////// 
// Function: try_grab 
// 
// Tries grabbing a channel for exclusive use and returns TRUE, if the channel was successfully
// grabbed by the scenario. Otherwise, it returns FALSE. 
// For more information on the channel grabbing rules, see the section <grab>.
// 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_scenario scenario_1 = new;
//|      bit grab_success;
//|   
//|      initial begin
//|         ...
//|         grab_success = chan.try_grab(scenario_1);
//|         if(grab_success == 0)
//|            `vmm_error(log, "scenario_1 could not grab the channel");
//|         else if(parent_grab == 1)
//|            `vmm_note(log, "scenario_1 has grabbed the channel ");
//|         ...
//|      end
//|   
//|   endprogram
function bit vmm_channel::try_grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.notify.is_on(PLAYBACK)) begin
      `vmm_warning(this.log, "Cannot grab a channel during playback");
      return 0;
   end

   if (this.check_all_grab_owners(grabber)) begin
      `vmm_warning(this.log, "Cannot grab a channel that is already grabbed by you");
      return 0;
   end
   
   if ((this.grab_owners.size() == 0) ||
       (this.check_grab_owners(grabber))) begin
        this.grab_owners.push_front(grabber);
        this.notify.indicate(GRABBED);
      return 1;
   end

   return 0;
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif //VMM_GRAB_DISABLED
endfunction: try_grab


// //////////////////////////////////////////// 
// 
// Task: grab 
// 
// Grabs a channel for the exclusive use of a scenario and its sub-scenarios. If the channel
// is currently grabbed by another scenario, the task blocks until the channel can be grabbed
// by the specified scenario descriptor. The channel will remain as grabbed, until it
// is released by calling the <ungrab> method. 
// If a channel is grabbed by a scenario that is a parent of the specified scenario, then
// the channel is immediately grabbed by the scenario. 
// If exclusive access to a channel is required outside of a scenario descriptor, then
// allocate a dummy scenario descriptor and use its reference. 
// When a channel is grabbed, the GRABBED notification is indicated. 
// Grabbing multiple channels creates a possible deadlock situation. 
// For example, two multi-stream scenarios may attempt to concurrently grab the same
// multiple channels, but in a different order. This may result in some of the channels
// to be grabbed by one of the scenario, and some of the channels to be grabbed by another
// scenario. This creates a deadlock situation, because neither scenario would eventually
// grab the remaining required channels. 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_scenario scenario_1 = new;
//|      my_scenario scenario_2 = new;
//|   
//|      initial begin
//|         ...
//|         chan.grab(scenario_1);
//|         ...
//|         chan.ungrab(scenario_1);
//|         chan.grab(scenario_2);
//|         ...
//|      end
//|   
//|   endprogram
task vmm_channel::grab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.notify.is_on(PLAYBACK)) begin
       this.notify.wait_for(vmm_channel::PLAYBACK_DONE);
   end

   if (this.grab_owners.size()==0) begin
      this.grab_owners.push_front(grabber);
      this.notify.indicate(GRABBED);
   end
   else begin
      if (this.check_all_grab_owners(grabber)) begin
         `vmm_error(this.log, "Cannot grab a channel that is already grabbed by you");
      end
      else if (this.check_grab_owners(grabber)) begin
         this.grab_owners.push_front(grabber);
         this.notify.indicate(GRABBED);
      end
      else begin
         this.notify.wait_for(vmm_channel::UNGRABBED);
         this.grab(grabber);
		 if(this.downstream != null)   // For channel which is connected
			 this.downstream.grab(grabber);

      end
   end
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif //VMM_GRAB_DISABLED

endtask: grab


// //////////////////////////////////////////// 
// 
// Task: ungrab 
// 
// Releases a channel that is previously grabbed for the exclusive use of a scenario, using
// the <grab> method. If another scenario is waiting to grab the channel,
// it will be immediately grabbed. 
// A channel must be explicitly ungrabbed, after the execution of an exclusive transaction
// stream is completed, to avoid creating deadlocks. 
// When a channel is ungrabbed, the UNGRABBED notification is indicated.
// 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_scenario scenario_1 = new;
//|      my_scenario scenario_2 = new;
//|   
//|      initial begin
//|         ...
//|         chan.grab(scenario_1);
//|         ...
//|         chan.ungrab(scenario_1);
//|         chan.grab(scenario_2);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_channel::ungrab(`VMM_SCENARIO grabber);
`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size()==0) begin
      `vmm_error(this.log, "Cannot ungrab a channel that is not grabbed!");
   end
   else begin
      if (grabber == this.grab_owners[0]) begin
         void'(this.grab_owners.pop_front());
         this.notify.indicate(UNGRABBED);
      end
      else begin
         `vmm_error(this.log, "Cannot ungrab a channel that you did not grab!");
      end
   end
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
`endif //VMM_GRAB_DISABLED
endfunction: ungrab


// //////////////////////////////////////////// 
// Function: is_grabbed 
// 
// Returns TRUE, if the channel is currently grabbed by a scenario. Otherwise, returns
// FALSE. 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_scenario scenario_1 = new;
//|      bit chan_status;
//|   
//|      initial begin
//|         ...
//|         chan_status = chan.is_grabbed();
//|         if(chan_status == 1)
//|            `vmm_note(log, "The channel is currently grabbed");
//|         else if(parent_grab == 0)
//|            `vmm_note(log, "The channel is currently not grabbed ");
//|         ...
//|      end
//|   
//|   endprogram
function bit vmm_channel::is_grabbed();
`ifndef VMM_GRAB_DISABLED
   return (this.grab_owners.size() > 0);
`else
   `vmm_error(this.log, "grab/ungrab functionality is not enabled");
   return 0;
`endif //VMM_GRAB_DISABLED
endfunction: is_grabbed


function void vmm_channel::display(string prefix="");
   $display(this.psdisplay(prefix));
endfunction: display


function string vmm_channel::psdisplay(string prefix="");
   $sformat(psdisplay, "%sChannel %s(%s): Level = %0d of %0d (empty=%0d)",
            prefix, this.log.get_name(), this.log.get_instance(),
            this.level(), this.full, this.empty);
   case (this.locks)
      SOURCE+SINK : psdisplay = {psdisplay, " [src+snk locked]"};
      SOURCE:       psdisplay = {psdisplay, " [src locked]"};
      SINK:         psdisplay = {psdisplay, " [snk locked]"};
   endcase
   if (this.is_sunk) psdisplay = {psdisplay, " (sunk)"};
`ifndef VMM_GRAB_DISABLED
   if (this.is_grabbed()) psdisplay = {psdisplay, " (grabbed by %s)",
                                       this.grab_owners[0].scenario_name(0)};
`endif

   foreach(this.data[i]) begin
      $sformat(psdisplay, "%s\n%s", psdisplay, this.data[i].psdisplay(`vmm_sformatf("%s   [%0d] ",
                                                                                    prefix, i)));
   end
endfunction: psdisplay


`ifndef VMM_GRAB_DISABLED
// //////////////////////////////////////////// 
// 
// Task: put 
// 
// Adds the specified transaction descriptor to the channel. If the channel is already
// full, or becomes full after adding the transaction descriptor, then the task will block
// until the channel becomes empty. 
// If an offset is specified, then the transaction descriptor is inserted in the channel
// at the specified offset. An offset of 0 specifies at the head of the channel (LIFO order).
// An offset of -1 indicates the end of the channel (FIFO order). 
// If the channel is currently grabbed by a scenario other than the one specified, then
// this method will block and not insert the specified transaction descriptor in the channel,
// until the channel is ungrabbed or grabbed by the specified scenario. 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_data md1 = new;
//|      my_scenario scenario_1 = new;
//|   
//|      initial begin
//|         ...
//|         chan.grab(scenario_1);
//|         chan.put(md1,scenario_1);
//|         ...
//|      end
//|   
//|   endprogram
task vmm_channel::put(vmm_data obj,
                      int offset=-1,
                      `VMM_SCENARIO grabber=null);
`else
task vmm_channel::put(vmm_data obj,
                      int offset=-1);
`endif //VMM_GRAB_DISABLED

   if (obj == null)
   begin
      `vmm_error(this.log, "Attempted to put null instance into channel");
      return;
   end // if obj == null

   if (offset >= 0 && this.full_chan) begin
      `vmm_warning(this.log, `vmm_sformatf("Cannot put at offset %0d in a full channel. Will appends at the end.", offset));
      offset = -1;
   end

`ifndef VMM_GRAB_DISABLED
   this.block_producer(grabber);
   this.is_put = 1'b1;
   this.sneak(obj, offset, grabber);
   this.is_put = 1'b0;
   this.block_producer(grabber);
`else
   this.block_producer();
   this.is_put = 1'b1;
   this.sneak(obj, offset);
   this.is_put = 1'b0;
   this.block_producer();
`endif
   if (flag_waiting) #0;

endtask: put


`ifndef VMM_GRAB_DISABLED
// //////////////////////////////////////////// 
// 
// Task: sneak 
// 
// Adds the specified transaction descriptor to the channel. This method will never block,
// even if the channel is full. An execution thread calling this method must contain some
// other throttling mechanism, to prevent an infinite loop from occurring. 
// This method is designed to be used in circumstances, where potentially blocking the
// execution thread could yield invalid results. For example, monitors must use this
// method to avoid missing observations. 
// If an offset is specified, the transaction descriptor is inserted in the channel at
// the specified offset. An offset of 0 specifies at the head of the channel (for example,
// LIFO order). An offset of -1 indicate the end of the channel (for example, FIFO order).
// 
// If the channel is currently grabbed by a scenario, other than the one specified, the
// transaction descriptor will not be inserted in the channel. 
// 
//|   
//|   class my_data extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_channel(my_data)
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_grab
//|   
//|      my_data_channel chan = new("Channel", "Grab", 10, 10);
//|      my_data md1 = new;
//|      my_scenario scenario_1 = new;
//|   
//|      initial begin
//|         ...
//|         chan.grab(scenario_1);
//|         chan.sneak(md1,,scenario_1); 
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_channel::sneak(vmm_data obj,
                                 int offset=-1,
                                 `VMM_SCENARIO grabber=null);
`else
function void vmm_channel::sneak(vmm_data obj,
                                 int offset=-1);
`endif //VMM_GRAB_DISABLED
   string txt;
   time diff_time;
   int id;

   if (obj == null)
   begin
      `vmm_error(this.log, "Attempted to sneak null instance into channel");
      return;
   end // obj == null
   if (this.is_locked(SOURCE|SINK) && !this.is_playback)
   begin
      `vmm_error(this.log, "Attempted to sneak when channel is locked");
      return;
   end // error on sneaking when locked
   
`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size() &&
       (this.check_grab_owners(grabber) == 0)) begin
      `vmm_error(this.log, "Attempted to sneak in a grabbed channel from a scenario that is not a current grabber");
      return;
   end
`endif //VMM_GRAB_DISABLED

   if (this.is_sunk == 0)
   begin

     if (offset == -1 || (offset == 0 && this.data.size() == 0))
     begin
        this.data.push_back(obj);
        id = 0;
     end
     else
     begin
        int idx = this.index(offset, "sneak()");
        if (idx < 0) return;

        this.data.insert(offset, obj);
        id = offset;
     end // if offset

     if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
     begin
       $sformat(txt, "New instance added to channel @%0d (level %0d of %0d/%0d)\n%s",
                offset, this.level(), this.full, this.empty,
                obj.psdisplay("    "));
        void'(this.log.text(txt));
        this.log.end_msg();
     end // if dbg

     // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
     vmm_tr_record::start_tr(this.top_stream, $psprintf("Tr[%0d]", id), obj.psdisplay(""));
     vmm_tr_record::start_tr(this.sub_stream, "[Put]", "");
     vmm_tr_record::end_tr(this.sub_stream);
`endif //VMM_TR_RECORD

     this.notify.indicate(PUT, obj);

     if (this.level() >= this.full)
     begin
        this.full_chan = 1;
        this.notify.indicate(FULL);
     end

     if (this.level() > this.empty)
     begin
        this.notify.reset(EMPTY);
     end
   end
   else
   begin
     //To make sure process watching channel do not get affected by sunk
     this.notify.indicate(PUT, obj);
     this.notify.indicate(GOT, obj);
   end
   
   //check fill threshhold
   if (do_object_thresh_check && this.level() >= fill_thresh) 
      `vmm_warning(this.log, `vmm_sformatf("The number of objects in the channel[%s] passes the specified threshold ( = %0d ) indicating a potential garbage collection/memory leak problem. Please use vmm_channel::sink() or increase the threshold.", this.log.get_instance(), fill_thresh));
         
   //recording
   if(this.notify.is_on(RECORDING))
   begin

     diff_time = $time - this.last_record_time;
     if(this.is_put == 1'b0)
       this.Xrecord_to_fileX(8'h02,offset,diff_time);
     else
       this.Xrecord_to_fileX(8'h01,offset,diff_time);

     //save object
     obj.save(this.record_fp);
     this.last_record_time = $time;
   end

   //Playback
   if(this.notify.is_on(PLAYBACK) && !this.is_playback)
   begin
     `vmm_warning(this.log,"vmm_channel::sneak accessed by source while playback is ON");
   end

   -> this.item_added;
endfunction: sneak


// //////////////////////////////////////////// 
// Function: unput 
// 
// It is an error to specify an offset to a transaction descriptor that does not exist. 
// This method may cause the EMPTY notification to be indicated, and causes the FULL notification
// to be reset. 
// 
function vmm_data vmm_channel::unput(int offset=-1);

   time diff_time;

   if (this.size() == 0) begin
      `vmm_error(this.log, "Cannot unput from an empty channel");
      return null;
   end // if size == 0

   if (offset == -1)
     unput = this.data.pop_back();
   else begin
     int idx = this.index(offset, "unput()");
     if (idx < 0)
        unput = null;
     else begin
        unput = this.data[idx];
        this.data.delete(idx);
     end
   end // if offset != -1

   if (unput != null) begin
      this.notify.indicate(GOT, unput);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         string txt;
         $sformat(txt, "Instance unput from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  unput.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.sub_stream, "[Unput]", unput.psdisplay(""));
      vmm_tr_record::end_tr(this.sub_stream);
      vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD

      // recording to output file
      if(this.notify.is_on(RECORDING))
      begin
        diff_time = $time - this.last_record_time;
        this.Xrecord_to_fileX(8'h03,offset,diff_time);
        this.last_record_time = $time;
      end

   end

   this.unblock_producer();
endfunction: unput

function void vmm_channel::Xrecord_to_fileX(bit [7:0] op_code,
                                            int offset,
                                            time diff_time);

   bit [7:0] bytes[13];
   bit [63:0] bit_conv;

   bytes[0] = op_code;

   bit_conv[31:0] = offset;
   bytes[1] = bit_conv[7:0];
   bytes[2] = bit_conv[15:8];
   bytes[3] = bit_conv[23:16];
   bytes[4] = bit_conv[31:24];

   bit_conv[63:0] = diff_time;
   bytes[5] = bit_conv[7:0];
   bytes[6] = bit_conv[15:8];
   bytes[7] = bit_conv[23:16];
   bytes[8] = bit_conv[31:24];
   bytes[9] = bit_conv[39:32];
   bytes[10] = bit_conv[47:40];
   bytes[11] = bit_conv[55:48];
   bytes[12] = bit_conv[63:56];

   //<1byte type><4byte offset><8byte time>
   foreach(bytes[i]) begin
     $fwrite(this.record_fp, "%c", bytes[i]);
   end
   //space
   if(op_code == 8'h03)
     $fwrite(this.record_fp, "\n");
   else
     $fwrite(this.record_fp, " ");

endfunction: Xrecord_to_fileX

function void vmm_channel::XgetX(output vmm_data obj,
                                 input  int      offset=0);
   this.X_getX(obj, offset);
   this.unblock_producer();
endfunction: XgetX

function void vmm_channel::X_getX(output vmm_data obj,
                                  input  int      offset=0);
`ifdef VMM_SB_DS_IN_STDLIB
   vmm_sb_ds _temp_sb;
`endif
   if (offset == 0)
      obj = this.data.pop_front();
   else begin
      int idx = this.index(offset, "get()");
      if (idx < 0)
         obj = null;
      else begin
         obj = this.data[idx];
         this.data.delete(idx);
      end // else if idx < 0
    end // else if offset

   if (obj != null) begin
      this.notify.indicate(GOT, obj);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         string txt;
         $sformat(txt, "New instance removed from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.sub_stream, "[Get]", obj.psdisplay(""));
      vmm_tr_record::end_tr(this.sub_stream);
      vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD

      if (this.tee_on) begin
         this.tee_data.push_back(obj);
         -> this.teed;
      end // tee_on

`ifdef VMM_SB_DS_IN_STDLIB
      foreach (this._vmm_sb_ds[i]) begin
         if (this._vmm_sb_ds[i].is_in) begin
            if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
               _temp_sb.insert(obj);
         end

         if (this._vmm_sb_ds[i].is_out) begin
            case (this._vmm_sb_ds[i].order)
              vmm_sb_ds::IN_ORDER:
                 if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
                    _temp_sb.expect_in_order(obj);

              vmm_sb_ds::WITH_LOSSES: begin
                 vmm_data p;
                 vmm_data losses[];
                 if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
                    _temp_sb.expect_with_losses(obj, p, losses);
              end

              vmm_sb_ds::OUT_ORDER:
                 if($cast(_temp_sb,this._vmm_sb_ds[i].sb))
                    _temp_sb.expect_out_of_order(obj);

            endcase
         end
      end
`endif //VMM_SB_DS_IN_STDLIB
   end // if obj != null
endfunction: X_getX

task vmm_channel::wait_for_request();
   if (chan_mode == PULL_MODE)
      req_bucket.get(1);
endtask

function void vmm_channel::set_mode(mode_e chan_mode);
   this.chan_mode = chan_mode;
endfunction: set_mode

// //////////////////////////////////////////// 
// 
// Task: get 
// 
// If the channel is empty, the function blocks until a transaction descriptor is available
// to be retrieved. This method may cause the EMPTY notification to be indicated, or the
// FULL notification to be reset. It is an error to invoke this method, with an offset value
// greater than the number of transaction descriptors, which are currently in the channel
// or with a non-empty active slot. 
// 
//|   
//|   virtual function void build();
//|      fork
//|         forever begin
//|            eth_frame fr;
//|            this.mac.rx_chan.get(fr);
//|            this.sb.received_by_phy_side(fr);
//|          end
//|      join_none
//|   endfunction: build
task vmm_channel::get(output vmm_data obj,
                      input  int      offset=0);
   int indx[$];
   int id;
   if (chan_mode == PULL_MODE) begin
      if (peek_q.size() != 0) begin
         indx = peek_q.find_first_index() with (item == offset);
         if (indx.size() != 0) begin
            id = indx[0];
            peek_q.delete(id);
         end
         else req_bucket.put(1);
      end
      else begin
         req_bucket.put(1);
      end
   end

   this.block_consumer();
   this.XgetX(obj, offset);
   this.unblock_producer();
endtask: get

// //////////////////////////////////////////// 
// 
// Task: peek 
// 
// Gets a reference to the next transaction descriptor that will be retrieved from the
// channel, at the specified offset, without actually retrieving it. If the channel is
// empty, then the function will block until a transaction descriptor is available to
// be retrieved. 
// It is an error to invoke this method with an offset value greater than the number of transaction
// descriptors currently in the channel, or with a non-empty active slot. 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      virtual task main();
//|         forever begin
//|            transaction tr;
//|            this.in_chan.peek(tr);
//|            this.in_chan.get(tr);
//|         end
//|      endtask: main
//|   endclass: consumer
task vmm_channel::peek(output vmm_data obj,
                       input  int      offset=0);
   string txt;
   int    idx;
   int indx[$];
   int id;
   
   if (chan_mode == PULL_MODE) begin
      if (peek_q.size() != 0) begin
         indx = peek_q.find_first_index() with (item == offset);
         if (indx.size() == 0) begin
            req_bucket.put(1);
            this.peek_q.push_back(offset);
         end
      end
      else begin
         req_bucket.put(1);
         this.peek_q.push_back(offset);
      end
   end
   this.block_consumer();

   idx = this.index(offset, "peek()");
   obj = (idx < 0) ? null : this.data[idx];

   if (obj != null) begin
      this.notify.indicate(PEEKED, obj);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
         $sformat(txt, "New instance peeked from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end 
      // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.sub_stream, "[Peek]", obj.psdisplay(""));
      vmm_tr_record::end_tr(this.sub_stream);
`endif //VMM_TR_RECORD
   end // obj != null

   this.unblock_producer();
endtask: peek


function vmm_data vmm_channel::try_peek(int offset = 0);
   string txt;
   int    idx;

   if (this.size() == 0 || this.is_locked(SINK)) return null;

   idx = this.index(offset, "try_peek()");
   if (idx < 0) return null;

   try_peek = this.data[idx];

   if (try_peek != null)
   begin
      this.notify.indicate(PEEKED, try_peek);
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         $sformat(txt, "New instance peeked from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  try_peek.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();

         // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
         vmm_tr_record::start_tr(this.sub_stream, "[TryPeek]", try_peek.psdisplay(""));
         vmm_tr_record::end_tr(this.sub_stream);
`endif //VMM_TR_RECORD
      end
   end
endfunction: try_peek


// //////////////////////////////////////////// 
// 
// Task: activate 
// 
// If the active slot is not empty, then this method first removes the transaction descriptor,
// which is currently in the active slot. 
// Move the transaction descriptor at the specified offset in the channel to the active
// slot ,and update the status of the active slot to PENDING. If the channel
// is empty, then this method will wait until a transaction descriptor becomes available.
// The transaction descriptor is still considered as being in the channel. 
// It is an error to invoke this method with an offset value greater than the number of transaction
// descriptors currently in the channel, or to use this method with multiple concurrent
// consumer threads. 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      ...
//|      virtual task main();
//|         ...
//|         forever begin
//|            transaction tr;
//|            ...
//|            this.in_chan.activate(tr);
//|            this.in_chan.start();
//|            ...
//|            this.in_chan.complete();
//|            this.in_chan.remove();
//|         end
//|      endtask: main
//|      ...
//|   endclass: consumer
task vmm_channel::activate(output vmm_data obj,
                           input  int      offset=0);
   string txt;
   int indx[$];
   int id;
   if (chan_mode == PULL_MODE) begin
      if (peek_q.size() != 0) begin
         indx = peek_q.find_first_index() with (item == offset);
         if (indx.size() != 0) begin
            id = indx[0];
            peek_q.delete(id);
         end
         else req_bucket.put(1);
      end
      else begin
         this.req_bucket.put(1);
      end
   end

   // Empty the active slot
   if (active != null)
      void'(this.remove());

   while (this.size() == 0)
      @this.item_added;

   if (offset == 0)
      obj = this.data.pop_front();
   else
   begin
      int idx = this.index(offset, "activate()");
      if (idx < 0)
      begin
        obj = null;
      end
      else
      begin
        obj = this.data[idx];
        this.data.delete(idx);
      end
   end // else if offset == 0


   if (obj != null)
   begin
      this.active = obj;
      this.active_status = PENDING ;
      this.notify.indicate(ACTIVATED, obj);
      this.notify.indicate(PEEKED, obj);

      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
      begin
         $sformat(txt, "New instance activated from channel @%0d (level %0d of %0d/%0d)\n%s",
                  offset, this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
         void'(this.log.text(txt));
         this.log.end_msg();
      end // if dbg_lvl

      // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.sub_stream, "[Activate]", obj.psdisplay(""));
      vmm_tr_record::end_tr(this.sub_stream);
      vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD

      if (this.tee_on)
      begin
         this.tee_data.push_back(obj);
         -> this.teed;
      end
   end // if obj != null

endtask: activate


// //////////////////////////////////////////// 
// Function: active_slot 
// 
// Returns the transaction descriptor, which is currently in the active slot. Returns
// null, if the active slot is empty. 
// 
function vmm_data vmm_channel::active_slot();
   active_slot = this.active;
endfunction: active_slot


// //////////////////////////////////////////// 
// Function: start 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      ...
//|      virtual task main();
//|         forever begin
//|            transaction tr;
//|            ...
//|            this.in_chan.activate(tr);
//|            this.in_chan.start();
//|            ...
//|            this.in_chan.complete();
//|            this.in_chan.remove();
//|         end
//|      endtask: main
//|      ...
//|   endclass: consumer
function vmm_data vmm_channel::start();
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot start() without prior activate()");
      return null;
   end // if active == null

   if (this.active_status == STARTED)
      `vmm_warning(this.log, "Active slot already start()'ed");

   this.active_status = STARTED;
   this.notify.indicate(ACT_STARTED, this.active);
`ifndef VMM_DATA_NO_NOTIFY_ALL
   this.active.notify.indicate(vmm_data::STARTED);
`endif // VMM_DATA_NO_NOTIFY_ALL
   start = this.active;
endfunction: start


// //////////////////////////////////////////// 
// Function: complete 
// 
// The transaction descriptor remains in the active slot, and may be restarted. It is an
// error to call this method, if the active slot is empty. The vmm_data::ENDED notification
// of the transaction descriptor in the active slot is indicated with the optionally specified
// completion status descriptor. 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      virtual task main();
//|         forever begin
//|            transaction tr;
//|            this.in_chan.activate(tr);
//|            this.in_chan.start();
//|            this.in_chan.complete();
//|            this.in_chan.remove();
//|         end
//|      endtask: main
//|   endclass: consumer
function vmm_data vmm_channel::complete(vmm_data status=null);
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot complete() without prior activate()");
      return null;
   end
   if (this.active_status != STARTED)
      `vmm_warning(this.log, "complete() called without start()");

   this.active_status = COMPLETED;
   this.notify.indicate(ACT_COMPLETED, this.active);
`ifndef VMM_DATA_NO_NOTIFY_ALL
   this.active.notify.indicate(vmm_data::ENDED, status);
`endif // VMM_DATA_NO_NOTIFY_ALL
   complete = this.active;
endfunction: complete


// //////////////////////////////////////////// 
// Function: remove 
// 
// Updates the status of the active slot to INACTIVE, and removes the transaction
// descriptor from the active slot from the channel. This method may cause the EMPTY notification
// to be indicated, or the FULL notification to be reset. It is an error to call this method
// with an active slot in the STARTED state. The vmm_data::ENDED notification
// of the transaction descriptor in the active slot is indicated. 
// 
//|   
//|   class consumer extends vmm_xactor;
//|      virtual task main();
//|         forever begin
//|            transaction tr;
//|            this.in_chan.activate(tr);
//|            this.in_chan.start();
//|            this.in_chan.complete();
//|            this.in_chan.remove();
//|         end
//|      endtask: main
//|   endclass: consumer
function vmm_data vmm_channel::remove();
   if (this.active == null)
   begin
      `vmm_fatal(this.log, "Cannot remove() without prior activate()");
      return null;
   end

   // OK to remove if not started or completed
   if (this.active_status == STARTED)
      `vmm_warning(this.log, "remove() called without complete()");

   this.notify.indicate(ACT_REMOVED, this.active);
   this.notify.indicate(GOT, this.active);
`ifndef VMM_DATA_NO_NOTIFY_ALL
   if (this.active_status != COMPLETED)
      this.active.notify.indicate(vmm_data::ENDED);
`endif // VMM_DATA_NO_NOTIFY_ALL
   this.active_status = INACTIVE;
   remove = this.active;
   this.active = null;

   this.unblock_producer();
endfunction: remove


// //////////////////////////////////////////// 
// Function: status 
// 
// Returns one of the enumerated values, as shown in Table A-4, indicating the status of
// the transaction descriptor in the active slot. 
// Pre-Configured Notifications in vmm_channel Notifier Interface 
// Symbolic Property Corresponding Significant Event 
// INACTIVE No transaction descriptor is present in the active slot. 
// PENDING A transaction descriptor is present in the active slot, but
// it is not started yet. 
// STARTED A transaction descriptor is present in the active slot, and
// it is started, but it is not completed yet. The transaction is being processed by the
// downstream transactor. 
// COMPLETED A transaction descriptor is present in the active slot, and
// it is processed by the downstream transactor, but it is not yet removed from the active
// slot. 
// 
// 
function vmm_channel::active_status_e vmm_channel::status();
   status = this.active_status;
endfunction: status


// //////////////////////////////////////////// 
// Function: tee_mode 
// 
// Returns TRUE, if the tee mode was previously ON. A thread that is blocked on a call to the
// <tee() method will not unblock execution, if the tee mode is turned OFF.
// If the stream of references is not drained through the tee> method, data
// will accumulate in the secondary channel when the tee mode is ON. 
// 
function bit vmm_channel::tee_mode(bit is_on);
   string txt;
   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV))
   begin
      $sformat(txt, "tee branch turned %0s", (is_on) ? "ON" : "OFF");
      void'(this.log.text(txt));
      this.log.end_msg();
   end

   tee_mode = this.tee_on;
   this.tee_on = is_on;
endfunction: tee_mode


// //////////////////////////////////////////// 
// 
// Task: tee 
// 
// When the tee mode is ON, retrieves a copy of the transaction descriptor references that
// is retrieved by the get() or activate() methods. The task blocks until one of the get()
// or activate() methods successfully completes. 
// This method can be used to fork off a second stream of references to the transaction descriptor
// stream. 
// The transaction descriptors themselves are not copied. 
// The references returned by this method are referring to the same transaction descriptor
// instances obtained by the get() and activate() methods. 
// 
task vmm_channel::tee(output vmm_data obj);
   string txt;
   
   while (this.tee_data.size() == 0)
      @this.teed;

   obj = this.tee_data.pop_front();

   if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV))
   begin
      $sformat(txt, "New instance teed from channel (level %0d of %0d/%0d)\n%s",
                  this.level(), this.full, this.empty,
                  obj.psdisplay("    "));
      void'(this.log.text(txt));
      this.log.end_msg();
   end

   // record transaction to VPD stream 
`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.sub_stream, "[Tee]", obj.psdisplay(""));
   vmm_tr_record::end_tr(this.sub_stream);
`endif //VMM_TR_RECORD

endtask: tee


// //////////////////////////////////////////// 
// Function: connect 
// 
// The connection is performed with a blocking model to communicate the status of the downstream
// channel, to the producer interface of the upstream channel. Flushing this channel
// causes the downstream connected channel to be flushed as well. However, flushing the
// downstream channel does not flush this channel. 
// The effective full and empty levels of the combined channels is equal to the sum of their
// respective levels minus one. However, the detailed blocking behavior of various interface
// methods differ from using a single channel, with an equivalent configuration. Additional
// zero-delay simulation cycles may be required, while transaction descriptors are
// transferred from the upstream channel to the downstream channel. 
// Connected channels need not be of the same type, but must carry compatible polymorphic
// data. 
// The connection of a channel into another channel can be dynamically modified and broken
// by connection to a null reference. However, modifying the connection while there is
// data flowing through the channels may yield unpredictable behavior. 
// 
function void vmm_channel::connect(vmm_channel downstream);

	// Do not disrupt an already-established connection
   if ( this.downstream == downstream )
		begin
		
			`vmm_trace(this.log, $psprintf("Attempt to connect two channels %s(%s) and %s(%s) which are already connected together", this.log.get_name(), this.log.get_instance(), downstream.log.get_name(), downstream.log.get_instance()));
	
			return;
		end


	if ( this.full_level != downstream.full_level)
		begin
			
			`vmm_fatal(this.log, $psprintf("Full level for upstream channel %s(%s) and downstream channel %s(%s) is not identical. \n Connection not established", this.log.get_name(), this.log.get_instance(), downstream.log.get_name(), downstream.log.get_instance()));

			return;			
		end	
	
	
	if (this.downstream != null)
		begin

			`vmm_fatal(this.log, $psprintf("Attempt to connect channel %s(%s) which is already connected", this.log.get_name(), this.log.get_instance()));

		end	

	if (downstream.downstream != null)
		begin

			`vmm_fatal(downstream.log, $psprintf("Attempt to connect channel %s(%s) which is already connected", downstream.log.get_name(), downstream.log.get_instance()));

		end

	
   // Indicate a new connection
   this.downstream = downstream;
   -> this.new_connection;

	if( downstream.get_consumer() != null)	
		this.set_consumer(downstream.get_consumer());
	
	if( downstream.get_producer() != null)	
		downstream.set_producer(this.get_producer());

endfunction: connect


// //////////////////////////////////////////// 
// Function: for_each 
// 
// The content of the active slot, if non-empty, is not included in the iteration. If the
// reset argument is TRUE, a reference to the first transaction descriptor in the channel
// is returned. Otherwise, a reference to the next transaction descriptor in the channel
// is returned. Returns null, when the last transaction descriptor in the channel is returned.
// It keeps returning null, unless reset. 
// Modifying the content of the channel in the middle of an iteration yields unexpected
// results. 
// 
function vmm_data vmm_channel::for_each(bit reset=0);
   if (reset) this.iterator = 0;
   else this.iterator++;

   if (this.iterator >= this.data.size()) for_each = null;
   else for_each = this.data[this.iterator];
endfunction: for_each


// //////////////////////////////////////////// 
// Function: for_each_offset 
// 
// Returns the offset of the last transaction descriptor, which is returned by the <for_each>
// method. An offset of 0 indicates the first transaction descriptor in the channel. 
// 
function int unsigned vmm_channel::for_each_offset();
   for_each_offset = this.iterator;
endfunction: for_each_offset


// //////////////////////////////////////////// 
// Function: record 
// 
// Starts recording the flow of transaction descriptors, which are added through the
// channel instance in the specified file. The <vmm_data::save() method must be implemented
// for that transaction descriptor, and defines the file format. A transaction descriptor
// is recorded, when added to the channel by the put> method. 
// A null filename stops the recording process. Returns TRUE, if the specified file was
// successfully opened. 
// 
function bit vmm_channel::record(string filename);
   if (filename == "")
   begin
      if(this.notify.is_on(RECORDING))
      begin
        $fclose(this.record_fp);
        this.notify.reset(RECORDING);
        return 1;
      end
      else
      begin
        `vmm_warning(this.log,"A valid 'filename' must be specified to start recording. vmm_channel::record() is ignoring call");
        return 0;
      end
   end
   else
   begin
     if(this.notify.is_on(RECORDING))
     begin
       `vmm_warning(this.log,"vmm_channel::record() is already started. Ignoring call");
       return 0;
     end
     else
     begin
       this.record_fp = $fopen(filename,"wb");
       if(this.record_fp == 0)
       begin
         `vmm_error(this.log,$psprintf("vmm_channel::record() is not able to open file: %s for recording",filename));
         this.record_fp = -1;
         return 0;
       end
       this.notify.indicate(RECORDING);
       this.last_record_time = $time;
       return 1;
     end
   end

endfunction: record

`ifndef VMM_GRAB_DISABLED
// //////////////////////////////////////////// 
// 
// Task: playback 
// 
// Injects the recorded transaction descriptors into the channel, in the same sequence
// in which they were recorded. The transaction descriptors are played back one-by-one,
// in the order found in the file. The recorded transaction stream replaces the producer
// for the channel. Playback does not need to happen in the same simulation run as recording.
// It can be executed in a different simulation run. 
// You must provide a non-null factory argument, of the same transaction descriptor type,
// as that with which recording was done. The <vmm_data::byte_unpack() or vmm_data::load>
// method must be implemented for the transaction descriptor passed in to the factory
// argument. 
// If the metered argument is TRUE, then the transaction descriptors are played back (that
// is, sneak, put, or unput-ed) to the channel in the same relative simulation time interval,
// as the one in which they were originally recorded. 
// While playing back a recorded transaction descriptor stream on a channel, all other
// sources of the channel are blocked (for example, <put() from any other
// source be blocked). Transactions added using the sneak> method would
// still be allowed from other sources, but a warning will be printed on any such attempt.
// 
// The success argument is set to TRUE, if the playback was successful. If the playback
// process encounters an error condition such as a NULL (empty string) filename, a corrupt
// file or an empty file, then success is set to FALSE. 
// When playback is completed, the PLAYBACK_DONE notification is indicated by notify.
// 
// If the channel is currently grabbed by a scenario, other than the one specified, the
// playback operation will be blocked until the channel is ungrabbed. 
// 
//|   
//|   class packet_env extends vmm_env;
//|      ...
//|      task start();
//|         ...
//|         `ifndef PLAY_DATA
//|            this.gen.start_xactor();
//|         `else
//|            fork
//|               begin
//|                  bit success;
//|                  data_packet factory = new;
//|                  this.gen.out_chan.playback(success,
//|                                             "stimulus.dat",
//|                                             factory, 1);
//|                  if (!this.success) begin
//|                     `vmm_error(this.log,
//|                                "Error during playback");
//|                  end
//|               end
//|            join_none
//|         `endif
//|      endtask
//|      ...
//|   endclass::packet_env
task vmm_channel::playback(output bit      success,
                           input  string   filename,
                           input  vmm_data factory,
                           input  bit      metered=0,
                           `VMM_SCENARIO   grabber=null);
`else
task vmm_channel::playback(output bit      success,
                           input  string   filename,
                           input  vmm_data factory,
                           input  bit      metered=0);
`endif //VMM_GRAB_DISABLED
   int playback_fp;
   bit [7:0] bytes[14];
   bit [7:0] op_code;
   bit [63:0] bit_conv;
   int offset;
   time time_delay;
   int data_id = 0;

`ifndef VMM_GRAB_DISABLED
   if (this.grab_owners.size() &&
      (this.check_grab_owners(grabber) == 0)) begin
      `vmm_error(this.log, "Cannot playback on a grabbed channel");
      return;
   end
`endif //VMM_GRAB_DISABLED

   this.notify.indicate(PLAYBACK);

   if(filename == "")
   begin
     success = 0;
     `vmm_error(this.log,"vmm_channel::playback() found null on input argument filename");
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   if(factory == null)
   begin
     success = 0;
     `vmm_error(this.log,"vmm_channel::playback() found null on input argument factory");
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   playback_fp = $fopen(filename,"rb");

   if(playback_fp == 0)
   begin
     success = 0;
     `vmm_error(this.log,$psprintf("vmm_channel::playback() can not open file %s: file does not exist",filename));
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   if($feof(playback_fp))
   begin
     $fclose(playback_fp);
     success = 0;
     `vmm_error(this.log,$psprintf("vmm_channel::playback() file %s is empty",filename));
     this.notify.reset(PLAYBACK);
     this.notify.indicate(PLAYBACK_DONE);
     return;
   end

   success = 1;

   this.lock(SOURCE);

   while(!$feof(playback_fp))
   begin
     foreach(bytes[i])
     begin
       int c = $fgetc(playback_fp);
       bytes[i] = c;
     end

     if(bytes[0] == 8'hff)
       break;

     op_code    = bytes[0];
     offset     = {bytes[4],bytes[3],bytes[2],bytes[1]};
     time_delay = {bytes[12],bytes[11],bytes[10],bytes[9],bytes[8],bytes[7],bytes[6],bytes[5]};

     if(op_code == 8'h01)
     begin
       if(!factory.load(playback_fp))
       begin
         `vmm_error(this.log,"vmm_data::load() failed");
         success = 0;
         break;
       end
       factory.data_id = data_id++;

       if(metered)
       begin
         #time_delay;
         this.is_playback = 1'b1;
         // If channel was sunk too fast, do our best
         if (offset >= this.size()) offset = -1;
`ifndef VMM_GRAB_DISABLED
         this.sneak(factory.copy(), offset, grabber);
`else
         this.sneak(factory.copy(), offset);
`endif
         this.is_playback = 1'b0;
       end
       else
         while (this.full_chan) @this.item_taken;
        // If channel was sunk too fast, do our best
        if (offset >= this.size()) offset = -1;
        this.is_playback = 1'b1;
`ifndef VMM_GRAB_DISABLED
        this.sneak(factory.copy(), offset, grabber);
`else
        this.sneak(factory.copy(), offset);
`endif
        this.is_playback = 1'b0;
        while (this.full_chan) @this.item_taken;
     end
     else if(op_code == 8'h02)
     begin
       if(!factory.load(playback_fp))
       begin
         `vmm_error(this.log,"vmm_data::load() failed");
         success = 0;
         break;
       end
       factory.data_id = data_id++;

       if(metered)
         #time_delay;

       this.is_playback = 1'b1;
       // If channel was sunk too fast, do our best
       if (offset >= this.size()) offset = -1;
`ifndef VMM_GRAB_DISABLED
       this.sneak(factory.copy(),offset, grabber);
`else
       this.sneak(factory.copy(),offset);
`endif
       this.is_playback = 1'b0;
     end
     else if(op_code == 8'h03)
     begin
       if(metered)
         #time_delay;
         // If channel was sunk too fast, do our best
         if (offset >= this.size()) offset = -1;
       if(this.unput(offset) == null)
         `vmm_warning(this.log,"vmm_channel::playback() found improper offset for unput operation");
     end
     else
     begin
       `vmm_error(this.log,$psprintf("vmm_channel::playback() file %s is corrupted",filename));
       success = 0;
       break;
     end
   end

   $fclose(playback_fp);
   this.unlock(SOURCE);
   this.notify.reset(PLAYBACK);
   this.notify.indicate(PLAYBACK_DONE);

endtask: playback


function int vmm_channel::index(int    offset,
                                string from);
   string txt;
   index = offset;
   if (offset < 0) index += this.data.size() + offset + 1;
   if (index < 0 || index >= this.data.size())
   begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV))
      begin
         $sformat(txt, "Invalid offset %0d specified in %s. Not in {0:%0d}.\n",
                  offset, from, this.data.size()-1);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      index = -1;
   end
endfunction: index


`ifndef VMM_GRAB_DISABLED
task vmm_channel::block_producer(`VMM_SCENARIO grabber);
    while (this.full_chan || this.is_locked(SOURCE) ||
          (this.grab_owners.size() &&
           (this.check_grab_owners(grabber) == 0))) begin
       fork
          begin
             if (this.grab_owners.size() &&
                 (this.check_grab_owners(grabber) == 0)) begin
                this.notify.wait_for(vmm_channel::UNGRABBED);
             end
          end
          begin
             if(this.full_chan) flag_waiting = flag_waiting + 1; 
             if(this.full_chan || this.is_locked(SOURCE)) begin
                @this.item_taken;
             end
          end
       join
   end
   if(flag_waiting !=0) flag_waiting = flag_waiting - 1;
`else
task vmm_channel::block_producer();
    if(this.full_chan) flag_waiting = flag_waiting + 1; 
    while (this.full_chan || this.is_locked(SOURCE))
       @this.item_taken;
    if(flag_waiting !=0) flag_waiting = flag_waiting - 1;
`endif //VMM_GRAB_DISABLED
endtask : block_producer


task vmm_channel::block_consumer();
   while (this.size() == 0 || this.is_locked(SINK))
      @this.item_added;
endtask: block_consumer


function void vmm_channel::unblock_producer();
   if (this.level() <= this.empty)
   begin
      this.full_chan = 0;
      this.notify.indicate(EMPTY);
   end

   if (this.level() < this.full)
      this.notify.reset(FULL);

   -> this.item_taken;
endfunction: unblock_producer


// //////////////////////////////////////////// 
// Function: get_producer 
// 
// Returns the transactor that is specified as the current producer, for the channel instance.
// Returns NULL, if no producer is identified. 
// 
//|   
//|   class tr extends vmm_data;
//|   endclass
//|   `vmm_channel(tr)
//|   
//|   class xactor extends vmm_xactor;
//|   endclass
//|   
//|   program prog;
//|      initial begin
//|         tr_atomic_gen agen = new("Atomic Gen");
//|         xactor xact = new("Xact", agen.out_chan);
//|         if (xact.in_chan.get_producer() != agen) begin
//|            `vmm_error(log, "Wrong producer for xact.in_chan");
//|         end
//|      end
//|   endprogram
function vmm_xactor vmm_channel::get_producer();
   get_producer = this.producer;
endfunction: get_producer


// //////////////////////////////////////////// 
// Function: get_consumer 
// 
// Returns the transactor that is specified as the current consumer for the channel instance.
// Returns NULL, if no consumer is identified. 
// 
//|   
//|   class tr extends vmm_data;
//|   endclass
//|   `vmm_channel(tr)
//|   
//|   class xactor extends vmm_xactor;
//|   endclass
//|   
//|   program prog;
//|      initial begin
//|         tr_atomic_gen agen = new("Atomic Gen");
//|         xactor xact = new("Xact", agen.out_chan);
//|         if (agen.out_chan.get_consumer() != xact) begin
//|            `vmm_error(log, "Wrong consumer for agen.out_chan");
//|         end
//|      end
//|   endprogram
function vmm_xactor vmm_channel::get_consumer();
   get_consumer = this.consumer;
endfunction: get_consumer


// //////////////////////////////////////////// 
// Function: set_producer 
// 
// Identifies the specified transactor as the current producer for the channel instance.
// This channel will be added to the list of output channels for the transactor. If a producer
// is previously identified, the channel instance is removed from the previous list of
// producer output channels. 
// Specifying a NULL transactor indicates that the channel does not contain any producer.
// 
// Although a channel can have multiple producers (even though with unpredictable ordering
// of each contribution of a producer to the channel, only one transactor can be identified
// as a producer of a channel, as they are primarily a point-to-point transaction-level
// connection mechanism. 
// 
//|   
//|   class tr extends vmm_data;
//|    ...
//|   endclass
//|   `vmm_channel(tr)
//|   `vmm_scenario_gen(tr, "tr")
//|   
//|   program prog;
//|   
//|      initial begin
//|         tr_scenario_gen sgen = new("Scen Gen");
//|         tr_channel chan1 = new("tr_channel", "chan1");
//|         ...
//|         chan1.set_producer(sgen);
//|         ...
//|      end
//|   endprogram
function void vmm_channel::set_producer(vmm_xactor producer);
   if (producer == null && this.producer == null) begin
      `vmm_error(this.log, "Attempted to set null producer");
      return;
   end

   if (this.producer == producer) return;
   
   if (this.producer != null) begin
      if(producer != null) begin
	 `vmm_warning(this.log, "Producer is already set");
      end
	  
`ifdef VCS
	   foreach(this.producer.Xoutput_chansX[i]) begin  
	      if (this.producer.Xoutput_chansX[i] == this) begin
	        this.producer.Xoutput_chansX.delete(i);
    	    break;
	      end
       end
	   `else  //Simplifying the code to ensure non VCS simulators can compile it 
	   for(int i =0; i < this.producer.Xoutput_chansX.size(); i++) begin
	      if (this.producer.Xoutput_chansX[i] == this) begin
	         this.producer.Xoutput_chansX.delete(i);
    	     break;
	      end
       end
	   `endif //ifdef VCS
   end
   this.producer = producer;
   if(producer != null) begin
     this.producer.Xoutput_chansX.push_back(this);
   end
endfunction: set_producer


// //////////////////////////////////////////// 
// Function: set_consumer 
// 
// Identifies the specified transactor as the current consumer for the channel instance.
// This channel will be added to the list of input channels for the transactor. If a consumer
// is previously identified, the channel instance is removed from the previous list of
// consumer input channels. 
// Specifying a NULL transactor indicates that the channel does not contain any consumer.
// 
// Although a channel can contain multiple consumers (even though with unpredictable
// distribution of input of each consumer from the channel, only one transactor can be
// identified as a consumer of a channel, as they are primarily a point-to-point transaction-level
// connection mechanism. 
// 
//|   
//|   class tr extends vmm_data;
//|    ...
//|   endclass
//|   `vmm_channel(tr)
//|   
//|   class xactor extends vmm_xactor;
//|      ...
//|   endclass
//|   
//|   program prog;
//|   
//|      initial begin
//|         xactor xact = new("xact");
//|         tr_channel chan1 = new("tr_channel", "chan1");
//|         ...
//|         chan1.set_consumer(xact);
//|         ...
//|      end
//|   endprogram
function void vmm_channel::set_consumer(vmm_xactor consumer);
   if (consumer == null && this.consumer == null) begin
      `vmm_error(this.log, "Attempted to set null consumer");
      return;
   end
   
   if (this.consumer == consumer) return;

   if (this.consumer != null) begin
      if (consumer != null) begin
	`vmm_warning(this.log, "Consumer is already set");
      end
	  
`ifdef VCS
	     foreach(this.consumer.Xinput_chansX[i]) begin
	        if (this.consumer.Xinput_chansX[i] == this) begin
			   this.consumer.Xinput_chansX.delete(i);
    	       break;
	        end
         end

	  `else //Simplifying the code to ensure non VCS simulators can compile it 
	     for(int i = 0; i < this.consumer.Xinput_chansX.size(); i++) begin
	        if (this.consumer.Xinput_chansX[i] == this) begin
			   this.consumer.Xinput_chansX.delete(i);
    	       break;
	        end
         end
	  `endif //ifdef VCS
    	    
   end
   this.consumer = consumer;
   if (consumer != null) begin
      this.consumer.Xinput_chansX.push_back(this);
   end
endfunction: set_consumer


// //////////////////////////////////////////// 
// Function: kill 
// 
// Prepares a channel for deletion and reclamation by the garbage collector. 
// Remove this channel instance from the list of input and output channels of the transactors,
// which are identified as its producer and consumer. 
// 
//|   
//|   program test_grab
//|      vmm_channel chan;
//|   
//|      initial begin
//|         chan = new("channel" ,"chan");
//|         ...
//|         chan.kill();
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_channel::kill();
   if (this.consumer != null) begin

`ifdef VCS
	      foreach(this.consumer.Xinput_chansX[i]) begin
             if(this.consumer.Xinput_chansX[i] == this) begin
    	        this.consumer.Xinput_chansX.delete(i);
    	        break;
             end
          end
	   `else //Simplifying the code to ensure non VCS simulators can compile it 
	      for(int i =0; i < this.consumer.Xinput_chansX.size(); i++) begin
             if(this.consumer.Xinput_chansX[i] == this) begin
    	        this.consumer.Xinput_chansX.delete(i);
    	        break;
             end
          end
	   `endif //ifdef VCS	  
   end

   if (this.producer != null) begin
	  
`ifdef VCS
	     foreach(this.producer.Xoutput_chansX[i]) begin   
            if (this.producer.Xoutput_chansX[i] == this) begin
	           this.producer.Xoutput_chansX.delete(i);
    	       break;
            end
         end
	  `else //Simplifying the code to ensure non VCS simulators can compile it 
	     for(int i = 0; i < this.producer.Xoutput_chansX.size(); i++) begin 
            if (this.producer.Xoutput_chansX[i] == this) begin
	           this.producer.Xoutput_chansX.delete(i);
    	       break;
            end
         end
	   `endif //ifdef VCS	 
   end

   this.downstream = null;
   -> this.new_connection;

   this.producer = null;
   this.consumer = null;

   if (this.shared_log == null) this.log.kill();
endfunction: kill   





`ifdef VMM_SB_DS_IN_STDLIB
function void vmm_channel::register_vmm_sb_ds(vmm_sb_ds_base             sb,
                                              vmm_sb_ds::kind_e     kind,
                                              vmm_sb_ds::ordering_e order=vmm_sb_ds::IN_ORDER);
   vmm_sb_ds_registration ds;

   if(sb == null) begin
     `vmm_error(this.log, "Trying to register null scoreboard");
     return;
   end 

   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         `vmm_warning(this.log, "Data stream scoreboard is already registered");
         return;
      end
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


function void vmm_channel::unregister_vmm_sb_ds(vmm_sb_ds_base sb);
   foreach (this._vmm_sb_ds[i]) begin
      if (this._vmm_sb_ds[i].sb == sb) begin
         this._vmm_sb_ds.delete(i);
         return;
      end
   end

   `vmm_error(this.log, "Data stream scoreboard is not registered");
endfunction: unregister_vmm_sb_ds
`endif //ifdef VMM_SB_DS_IN_STDLIB

