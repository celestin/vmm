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
// Class: vmm_broadcast
//
// Channels are point-to-point data transfer mechanisms. If multiple consumers are 
// extracting transaction descriptors from a channel, the transaction descriptors 
// are distributed among various consumers and each of the N consumers view 1/N descriptors. 
// If a point-to-multi-point mechanism is required, where all consumers must view all 
// transaction descriptors in the stream, then a vmm_broadcast component can be used 
// to replicate the stream of transaction descriptors from a source channel to an 
// arbitrary and dynamic number of output channels. 
// If only two output channels are required, the <vmm_channel::tee()> method of the 
// source channel may also be used.
//
// You can configure individual output channels to receive a copy of the reference 
// to the source transaction descriptor (most efficient but the same descriptor 
// instance is shared by the source and all like-configured output channels) or 
// to use a new descriptor instance copied from the source object (least efficient 
// but uses a separate instance that can be modified without affecting other 
// channels or the original descriptor). A vmm_broadcast component can be configured 
// to use references or copies in output channels by default.
//
// In the As Fast As Possible (AFAP) mode, the full level of output channels is ignored. 
// Only the full level of the source channel controls the flow of data through the 
// broadcaster. Output channels are kept non-empty, as much as possible. As soon as 
// an active output channel becomes empty, the next descriptor is removed from the 
// source channel (if available), and added to all output channels, even if they are already full.
//  
// Function: new 
// 
// Creates a new instance of a channel broadcaster object with the specified name, instance
// name, source channel, and broadcasting mode. If use_references is TRUE (that is, non-zero),
// references to the original source transaction descriptors are assigned to output
// channels by default (unless individual output channels are configured otherwise).
// 
//|     vmm_broadcast bcast = new("Bcast", "", in_chan, 1);
//
function vmm_broadcast::new(string      name,
                            string      inst,
                            vmm_channel source,
                            bit         use_references=1,
                            int         mode=AFAP
                            `VMM12_XACTOR_NEW_EXTERN_ARGS `VMM_XACTOR_NEW_EXTERN_ARGS);
   super.new(name, inst, -1 `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL);
   
   this.in_chan       = source;
   if (in_chan != null)
     this.log.is_above(this.in_chan.log);
   this.dflt_use_refs = use_references;
   this.mode          = mode;

   this.n_out_chans = 0;
endfunction : new


function string vmm_broadcast::psdisplay(string prefix = "");
   psdisplay = super.psdisplay(prefix);
   $sformat(psdisplay, "%s [Mode: %s]", psdisplay,
            (this.mode == ALAP) ? "ALAP" : "AFAP");
   $sformat(psdisplay, "%s\n%sInpChan: %s(%s) [level=%0d of %0d]",
            psdisplay, prefix, this.in_chan.log.get_name(),
            this.in_chan.log.get_instance(), this.in_chan.level(),
            this.in_chan.full_level());
   foreach (this.out_chans[i]) begin
      $sformat(psdisplay, "%s\n%sOutChan[%0d/%s/%s]: %s(%s) [level=%0d of %0d]",
               psdisplay, prefix, i, (this.is_on[i]) ? "ON " : "OFF",
               (this.use_refs[i]) ? "ref" : "cpy",
               this.out_chans[i].log.get_name(),
               this.out_chans[i].log.get_instance(), this.out_chans[i].level(),
               this.out_chans[i].full_level());
   end
   return psdisplay;
endfunction


// //////////////////////////////////////////// 
// Function: broadcast_mode 
// 
// The new mode takes effect immediately. The available modes are specified by using one
// of the class-level enumerated symbolic values shown in Table A-1. 
// Broadcasting Mode Enumerated Values 
// Enumerated Value Broadcasting Operation 
// ALAP As Late As Possible. 
// Data is broadcast only when all active output channels are empty. This delay ensures
// that data is not broadcast any faster than the slowest of all consumers can digest it.
// 
// AFAP As Fast As Possible. 
// Active output channels are kept non-empty, as much as possible. As soon as an active
// output channel becomes empty, the next descriptor from the input channel (if available)
// is immediately broadcast to all active output channels, regardless of their fill level
// 
// 
// This mode must not be used if the data source can produce data at a higher rate than the
// slowest data consumer, and if broadcast data in all output channels are not consumed
// at the same average rate. 
// 
// 
task vmm_broadcast::broadcast_mode(bcast_mode_e mode);
   if (mode != AFAP && mode != ALAP) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text(`vmm_sformatf("Invalid broadcast mode %0d", mode)));
         this.log.end_msg();
      end
      return;
   end
   
   this.mode = mode;
   // This MAY create the opportunity for a new broadcast cycle...
   -> this.new_cycle;
endtask : broadcast_mode


// //////////////////////////////////////////// 
// Function: new_output 
// 
// 
// Adds the specified channel instance as a new output channel to the broadcaster. If use_references
// is TRUE (that is, non-zero), references to the original source transaction descriptor
// is added to the output channel. If FALSE (that is, zero), a new instance copied from the
// original source descriptor is added to the output channel. If unknown (that is, 1'bx),
// the default broadcaster configuration is used. 
// If there are no output channels, the data from the input channel is continuously drained
// to avoid data accumulation. 
// This method returns a unique identifier for the output channel that must be used to modify
// the configuration of the output channel. 
// Any user extension of this method must call super.new_output(). 
// 
function int vmm_broadcast::new_output(vmm_channel channel,
                                       logic use_references=1'bx);
   int     chan_id = this.n_out_chans++;
   
   if(channel == null) begin
     `vmm_error(this.log,"Null argument provided to vmm_broadcast::new_output");
     return 0;
   end

   this.out_chans.push_back(channel);
   this.is_on.push_back(1);
   this.use_refs.push_back((use_references === 1'bx) ?
                           this.dflt_use_refs : use_references);


   // Trigger a new broadcasting cycle whenever the channel becomes
   // empty while it is ON
   fork
      while (1) begin
         // A new (presumably empty) channel is added creates
         // a broadcast opportunity
         if (this.is_on[chan_id]) -> this.new_cycle;
         channel.notify.wait_for(vmm_channel::GOT);
      end
   join_none

   new_output = chan_id;
endfunction : new_output


function void vmm_broadcast::set_input(vmm_channel source);
   if (in_chan == null) begin
      in_chan = source;
      this.log.is_above(this.in_chan.log);
   end else begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         void'(this.log.text("Source channel already set, ignoring set_input call"));
         this.log.end_msg();
      end
   end
endfunction : set_input


// //////////////////////////////////////////// 
// Function: bcast_on 
// 
// By default, broadcasting to an output channel is on. When broadcasting is turned off,
// the output channel is flushed and the addition of new transaction descriptors from
// the source channel is inhibited. The addition of descriptors from the source channel
// is resumed, as soon as broadcasting is turned on. 
// If all output channels are off, the input channel is continuously drained to avoid data
// accumulation. 
// Any user extension of these methods should call super.bcast_on(). 
// 
function void vmm_broadcast::bcast_on(int unsigned output_id);
   this.bcast_on_off(output_id, 1);
endfunction: bcast_on   


// //////////////////////////////////////////// 
// Function: bcast_off 
// 
// By default, broadcasting to an output channel is on. When broadcasting is turned off,
// the output channel is flushed and the addition of new transaction descriptors from
// the source channel is inhibited. The addition of descriptors from the source channel
// is resumed, as soon as broadcasting is turned on. 
// If all output channels are off, the input channel is continuously drained to avoid data
// accumulation. 
// Any user extension of this method should call super.bcast_off(). 
// 
function void vmm_broadcast::bcast_off(int unsigned output_id);
   this.bcast_on_off(output_id, 0);
endfunction: bcast_off


function void vmm_broadcast::bcast_on_off(int     channel_id,
                                          int     on_off);
   if (channel_id < 0 || channel_id >= this.n_out_chans) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP)) begin
         string txt;
         $sformat(txt, "Invalid output channel ID %0d", channel_id);
         void'(this.log.text(txt));
         this.log.end_msg();
      end
      return;
   end

   this.is_on[channel_id] = on_off;

   // If a non-full channel is turned back on, this triggers a
   // new broadcasting cycle
   if (on_off && !this.out_chans[channel_id].is_full()) begin
      -> this.new_cycle;
   end

   // If a full channel is turned off, this triggers a
   // new broadcasting cycle
   if (!on_off && this.out_chans[channel_id].is_full()) begin
      -> this.new_cycle;
   end

   // Flush a channel that has been turned off
   if (!on_off) begin
      this.out_chans[channel_id].flush();
   end
endfunction: bcast_on_off


task vmm_broadcast::bcast_to_output(int     channel_id,
                                    int     on_off);
   this.bcast_on_off(channel_id, on_off);
endtask : bcast_to_output


// //////////////////////////////////////////// 
// Function: add_to_output 
// 
// Overloading this method, allows the creation of broadcaster components with different
// broadcasting rules. If this function returns TRUE (that is, non-zero), then the transaction
// descriptor will be added to the specified output channel. If this function returns
// FALSE (that is, zero), then the descriptor is not added to the channel. If the output
// channel is configured to use new descriptor instances, the obj parameter is a reference
// to that new instance. 
// This method is not necessarily invoked in increasing order of output identifiers.
// It is only called for output channels currently configured as ON. If this method returns
// FALSE for all output channels, for a given broadcasting cycle, lock-up may occur. The
// decision_id argument is reset to 0 at the start of every broadcasting cycle, and is incremented
// after each call to this method in the same cycle. It can be used to identify the start of
// broadcasting cycles. 
// If transaction descriptors are manually added to output channels, it is important
// that the <vmm_channel::sneak> method be used to prevent the execution thread from
// blocking. It is also important that FALSE be returned to prevent that descriptor from
// being added to that output channel by the default broadcast operations, and thus from
// being duplicated into the output channel. 
// The default implementation of this method always returns TRUE. 
// 
function bit vmm_broadcast::add_to_output(int unsigned decision_id,
                                          int unsigned output_id,
                                          vmm_channel  channel,
                                          vmm_data     obj);
   add_to_output = 1;
endfunction : add_to_output


// //////////////////////////////////////////// 
// Function: start_xactor 
// 
// The broadcaster can be stopped. Any extension of this method must call super.start_xactor().
// 
// 
//|   
//|      vmm_broadcast bcast = new("Bcast", "", in_chan, 1);
//|      bcast.start_xactor();
function void vmm_broadcast::start_xactor();
   super.start_xactor();
   if (in_chan == null) begin
      if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) begin
         void'(this.log.text("Broadcast started but source channel is not yet set"));
         this.log.end_msg();
      end
   end
endfunction : start_xactor


function void vmm_broadcast::stop_xactor();
   super.stop_xactor();
endfunction : stop_xactor


// //////////////////////////////////////////// 
// Function: reset_xactor 
// 
// The broadcaster can be restarted. The input channel and all output channels are flushed.
// 
// 
function void vmm_broadcast::reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
   super.reset_xactor(rst_typ);
   
   this.in_chan.flush();
   foreach (out_chans[i]) begin
      this.out_chans[i].flush();
   end
endfunction : reset_xactor


task vmm_broadcast::main();
   fork
      super.main();
      this.update_xactor_notifications();
      this.broadcast();
      this.sink_if_outs();
   join_none
endtask : main

task vmm_broadcast::update_xactor_notifications();
   while (1) begin
      bit all_channels_empty = 1;
      
      // Wait for all channels to get empty
      this.in_chan.notify.wait_for(vmm_channel::EMPTY);
      foreach (this.out_chans[i]) begin
         this.out_chans[i].notify.wait_for(vmm_channel::EMPTY);
      end

      // Make sure all i/o channels are still empty.
      if (this.in_chan.level() != 0) begin
         all_channels_empty = 0;
      end 
      if (all_channels_empty) begin
         foreach (this.out_chans[i]) begin
            if (this.out_chans[i].level() != 0) begin
               all_channels_empty = 0;
            end
         end
      end

      if (all_channels_empty) begin
         this.notify.indicate(vmm_xactor::XACTOR_IDLE);
         this.notify.reset(vmm_xactor::XACTOR_BUSY);

         // Wait for new broadcast data to flow in 
         this.in_chan.notify.wait_for_off(vmm_channel::EMPTY);
         this.notify.indicate(vmm_xactor::XACTOR_BUSY);
         this.notify.reset(vmm_xactor::XACTOR_IDLE);
      end
   end
endtask


task vmm_broadcast::broadcast();
   bit run_once = 1;

   while (1) begin
      int     decision_id = 0;
      int     i;
      int     go;
      
      vmm_data data, cpy;
      vmm_data obj;
      
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("Waiting for next broadcasting cycle..."));
         this.log.end_msg();
      end
      if (!run_once)  @ this.new_cycle;
      run_once = 0;
      this.wait_if_stopped();

      // OK to broadcast?
      case (this.mode) 

         AFAP: begin
            // OK to broadcast if just one active output channel
            // is not full
            int     i;

            go = 0;
            for (i = 0; i < this.n_out_chans; i++) begin
               if (this.is_on[i] && !this.out_chans[i].is_full()) begin
                  go = 1;
                  break;
               end
            end
         end
         
         ALAP: begin
            // OK to broadcast only if ALL active output channel
            // are not full
            int     i;
            
            go = 1;
            for (i = 0; i < this.n_out_chans; i++) begin
               if (this.is_on[i] && this.out_chans[i].is_full()) begin
                  go = 0;
                  break;
               end
            end
         end

         default: begin
            `vmm_error(this.log, `vmm_sformatf("Internal Error: Invalid broadcasting mode %0d!", this.mode));
            continue;
         end
      endcase
      // No go!
      if (!go) continue;
      
      this.wait_if_stopped();
      this.in_chan.get(data);
      this.wait_if_stopped();
       
`ifdef VMM_DETAILED_MSGS
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::TRACE_SEV)) begin
         void'(this.log.text("New broadcasting cycle..."));
         this.log.end_msg();
      end
      if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::VERBOSE_SEV)) begin
         void'(this.log.text(data.psdisplay("Broadcasting:")));
         this.log.end_msg();
      end
`endif

      for (i = 0; i < this.n_out_chans; i++) begin
         if (this.is_on[i]) begin

            // Copy or reference?
            if (this.use_refs[i]) begin
                obj = data;
            end
            else begin
               // Minimize the number of copies made
               if (cpy == null) cpy = data.copy();
               obj = cpy;
            end
            
            if (this.add_to_output(decision_id++, i, this.out_chans[i], obj)) begin
               this.out_chans[i].sneak(obj);
`ifdef VMM_DETAILED_MSGS
               if (this.log.start_msg(vmm_log::INTERNAL_TYP,
                                      vmm_log::DEBUG_SEV)) begin
                  string msg;
                  $sformat(msg, "Broadcasted to output #%0d", i);
                  void'(this.log.text(msg));
                  this.log.end_msg();
               end
               if (this.log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::VERBOSE_SEV)) begin
                  void'(this.log.text(obj.psdisplay("Broadcasted:")));
                  this.log.end_msg();
               end
`endif
               // Mark the copy as having been used.
               if (!this.use_refs[i]) cpy = null;
            end
         end
      end
   end
endtask : broadcast 


task vmm_broadcast::sink_if_outs();
   bit sink;
   vmm_data unused_data;
   
   vmm_data temp_obj;
   // Sink the data from the source channel
   // if there are no active output channels
   while (1) begin
      int     i;

      // Wait for something to be in the source channel
      vmm_data peeked;
      this.in_chan.peek(peeked);

      // Can it go anywhere??
      sink = 1;
      for (i = 0; i < this.n_out_chans; i++) begin
         if (this.is_on[i]) begin
            sink = 0;
            break;
         end
      end

      // Sink it if there is nowhere to go and it has not
      // been removed by some other thread.
      this.in_chan.peek( temp_obj);
      if (sink && this.in_chan.level() > 0 &&
          temp_obj == peeked ) begin
         this.in_chan.get( unused_data);
      end

      if (in_chan.level() > 0) begin
         in_chan.notify.wait_for(vmm_channel::GOT);
      end
   end
endtask : sink_if_outs
