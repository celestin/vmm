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


`ifndef VMM_CONSENSUS__SV
`define VMM_CONSENSUS__SV


// //////////////////////////////////////////// 
// Class: vmm_consensus 
//
// This class is used to determine when all the elements of a testcase, a verification environment, 
// or a sub-environment agree that the test may be terminated.
//  
// Function: new 
// 
// Creates a new instance of this class with the specified name and instance name. The specified
// name and instance names are used as the name and instance names of the log class property.
// You can pass a massage service interface(log) to consensus through constructor, if
// log is not being passed the it will create a new instance of log. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|      end
//|   endprogram
function vmm_consensus::new(string        name,
                            string        inst,
			    vmm_log       log=null);
`ifdef VMM_CONSENSUS_BASE_NEW_CALL
   super.new(`VMM_CONSENSUS_BASE_NEW_CALL);
`endif

   this.Xis_sub_consensusX = 0;
   this.Xparent_voterX = null;
   this.reg_voter_frm_reg_consensus = 0;

   if(log == null)
`ifdef VMM_12_UNDERPIN_VMM_CONSENSUS
      this.log = new(name, this.get_object_hiername());
`else
      this.log = new(name, inst);
`endif
   else
      this.log = log;
   this.notify = new(log);
   void'(this.notify.configure(NEW_VOTE));
`ifdef ENABLE_VMM_CONSENSUS__REACHED
   void'(this.notify.configure(REACHED, vmm_notify::ON_OFF));
`endif
   void'(this.notify.configure(REQUEST));

   this.n_dissenters = 0;
   this.n_forcing    = 0;
   this.upward       = null;
`ifdef ENABLE_VMM_CONSENSUS__REACHED
   this.notify.indicate(REACHED);
`endif
endfunction: new


// //////////////////////////////////////////// 
// Function: register_voter 
// 
// Creates a new general-purpose voter interface that can participate in this consensus.
// The specified argument name indicates the name of a voter. By default, a voter opposes
// the end of test. The voter interface may be later unregistered from the consensus using
// the <unregister_voter> method. 
// For more information on the general-purpose participant interface, see the section
// vmm_voter. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_voter v1;
//|         ...
//|         v1 = vote.register_voter("Voter #1");
//|         ...
//|      end
//|   endprogram
function vmm_voter vmm_consensus::register_voter(string name);
   bit sub_consensus_needs_update = 0;
   vmm_voter voter = new(name, this);

   if (!this.reg_voter_frm_reg_consensus && this.Xis_sub_consensusX) begin
      if (this.n_forcing == 0 && this.n_dissenters == 0) 
         sub_consensus_needs_update = 1;
   end

   // Voters object by default
   this.n_dissenters++;

   this.voters.push_back(voter);

   if (!this.reg_voter_frm_reg_consensus &&
        this.Xis_sub_consensusX && sub_consensus_needs_update) begin
      this.Xparent_voterX.update_vote();
   end

   return voter;
endfunction: register_voter


// //////////////////////////////////////////// 
// 
// Task: unregister_voter 
// 
// Removes a previously registered general-purpose voter interface from this consensus.
// If the voter was the only participant that objected to the consensus, the consensus
// will subsequently be reached. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_voter v1;
//|         ...
//|         v1 = vote.register_voter("Voter #1");
//|         ...
//|         vote.unregister_voter(v1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::unregister_voter(vmm_voter voter);
   foreach (this.voters[i]) begin
      if (this.voters[i] == voter) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {voter.get_name(), " is not a registered voter"});
endfunction: unregister_voter


// //////////////////////////////////////////// 
// 
// Task: register_xactor 
// 
// Adds a transactor that can participate in this consensus. A transactor opposes the
// end-of-test, if it is currently indicating the <vmm_xactor::IS_BUSY notification.
// Moreover, it consents to the end of test, if it is currently indicating the vmm_xactor::IS_IDLE
// notification. The transactor may be later unregistered from the consensus using the
// unregister_xactor> method. 
// 
//|   
//|   program test_consensus;
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_xactor v1 =new("Voter", "#1");
//|         ...
//|         vote.register_xactor(v1);
//|         ...
//|      end
//|   endprogram
function void vmm_consensus::register_xactor(vmm_xactor xact);
   vmm_voter voter;
   if(xact == null) begin
     `vmm_error(this.log,"Trying to register null vmm_xactor reference");
     return;
   end
   voter = this.register_voter({"Transactor ", xact.get_name(),
                                          "(", xact.get_instance(), ")"});
   voter.xactor(xact);
endfunction: register_xactor


// //////////////////////////////////////////// 
// 
// Task: unregister_xactor 
// 
// Removes a previously registered transactor from this consensus. If the transactor
// was the only participant that objected to the consensus, then the consensus will subsequently
// be reached. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_xactor v1 =new("Voter", "#1");
//|         ...
//|         vote.register_xactor(v1);
//|         ...
//|         vote.unregister_xactor(v1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::unregister_xactor(vmm_xactor xact);
   foreach (this.voters[i]) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_xactor() == xact) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Transactor ", xact.get_name(), "(",
                         xact.get_instance(), ") is not a registered voter"});
endfunction: unregister_xactor


// //////////////////////////////////////////// 
// 
// Task: register_channel 
// 
// Adds a channel that can participate in this consensus. By default, a channel opposes
// the end of test if it is not empty, and consents to the end of test if it is currently empty.
// The channel may be later unregistered from the consensus using the <unregister_channel>
// method. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_channel v1 =new("Voter", "#1");
//|         ...
//|         vote.register_channel(v1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::register_channel(vmm_channel chan);
   vmm_voter voter;
   if(chan == null) begin
     `vmm_error(this.log,"Trying to register null vmm_channel reference");
     return;
   end
   voter = this.register_voter({"Channel ",
                                chan.log.get_name(), "(",
                                chan.log.get_instance(), ")"});
   voter.channel(chan);
endfunction: register_channel


// //////////////////////////////////////////// 
// 
// Task: unregister_channel 
// 
// Removes a previously registered channel from this consensus. If the channel was the
// only participant that objected to the consensus, the consensus will subsequently
// be reached. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_channel v1 =new("Voter", "#1");
//|         ...
//|         vote.register_channel(v1);
//|         ...
//|         vote.unregister_channel(v1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::unregister_channel(vmm_channel chan);
   foreach (this.voters[i]) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_channel() == chan) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Channel ", chan.log.get_name(), "(",
                         chan.log.get_instance(),
                         ") is not a registered voter"});
endfunction: unregister_channel


// //////////////////////////////////////////// 
// 
// Task: register_notification 
// 
// Adds an ON or OFF notification that can participate in this consensus. The specified
// argument notify is the handle of <vmm_notify class under which specified notification
// is registered. By default, a notification opposes the end of test if it is not indicated,
// and consents to the end of test if it is currently indicated. The notification may be
// later unregistered from the consensus using the unregister_notification>
// method. 
// For more information on opposite polarity participation, see the <register_no_notification>
// method. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_notify v1;
//|         vmm_log notify_log;
//|         notify_log = new ("Voter", "#1");
//|         v1 = new (notify_log);
//|         v1.configure(1, vmm_notify::ON_OFF);
//|         ...
//|         vote.register_notification(v1,1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::register_notification(vmm_notify notify,
                                                   int notification);

   vmm_voter voter;
   string    name;
   int       mode;

   if (notify == null) begin
      `vmm_error(this.log, "Cannot register NULL vmm_notify reference");
      return;
   end

   mode = notify.is_configured(notification);
   if (!mode) begin
      `vmm_error(this.log, "Cannot register unconfigured notification");
      return;
   end
   if (mode != vmm_notify::ON_OFF) begin
      `vmm_error(this.log, "Can only register ON_OFF notification");
      return;
   end

   $sformat(name, "Notification #%0d %s(%s)",
            notification, notify.log.get_name(),
            notify.log.get_instance());
   voter = this.register_voter(name);
   voter.notify(notify, notification, 1);
endfunction: register_notification


// //////////////////////////////////////////// 
// 
// Task: register_no_notification 
// 
// Adds an ON or OFF notification that can participate in this consensus. By default, a
// notification opposes the end of test if it is indicated, and consents to the end of test
// if it is not currently indicated. The notification may be later unregistered from the
// consensus using the <unregister_notification> method. 
// For more information on the opposite polarity participation, see the section, <register_notification>.
// 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_notify v1;
//|         vmm_log notify_log;
//|         notify_log = new ("Voter", "#1");
//|         v1 = new (notify_log);
//|         v1.configure(1, vmm_notify::ON_OFF);
//|         ...
//|         vote.register_no_notification(v1,1);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::register_no_notification(vmm_notify notify,
                                                      int notification);

   vmm_voter voter;
   string    name;
   int       mode;

   if (notify == null) begin
      `vmm_error(this.log, "Cannot register NULL vmm_notify reference");
      return;
   end

   mode = notify.is_configured(notification);
   if (!mode) begin
      `vmm_error(this.log, "Cannot register unconfigured notification");
      return;
   end
   if (mode != vmm_notify::ON_OFF) begin
      `vmm_error(this.log, "Can only register ON_OFF notification");
      return;
   end

   $sformat(name, "Notification #%0d %s(%s)",
            notification, notify.log.get_name(),
            notify.log.get_instance());
   voter = this.register_voter(name);
   voter.notify(notify, notification, 0);
endfunction: register_no_notification


// //////////////////////////////////////////// 
// 
// Task: unregister_notification 
// 
// Removes a previously registered ON or OFF notification from this consensus. The specified
// argument notify is the handle of vmm_notify class under which specified notification
// is registered. If the notification was the only participant that objected to the consensus,
// the consensus will subsequently be reached. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_notify v1;
//|         vmm_log notify_log;
//|         notify_log = new ("Voter", "#1");
//|         v1 = new (notify_log);
//|         v1.configure(1, vmm_notify::ON_OFF);
//|         vote.register_notification(v1,1);
//|         vote.unregister_notification(v1,1);
//|      end
//|   endprogram
function void vmm_consensus::unregister_notification(vmm_notify notify,
                                                     int notification);
   foreach (this.voters[i]) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_notify() == notify &&
          voter.get_notification() == notification) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   begin
      string msg;
      $sformat(msg, "Notification #%0d %s(%s) is not registered with the consensus",
               notification, notify.log.get_name(),
               notify.log.get_instance());
      `vmm_error(this.log, msg);
   end
endfunction: unregister_notification


// //////////////////////////////////////////// 
// 
// Task: register_consensus 
// 
// Adds a sub-consensus that can participate in this consensus. By default, a sub-consensus
// opposes the higher-level end of test if it is not reached its own consensus. Also, it
// consents to the higher-level end of test, if it is reached (or forced) its own consensus.
// The sub-consensus may be later unregistered from the consensus, using the <unregister_consensus>
// method. 
// By default, a sub-consensus that has reached its consensus by force will not force a
// higher-level consensus, only consent to it. If the force_through parameter is specified
// as non-zero, a forced sub-consensus will force a higher-level consensus. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_consensus c1;
//|         c1 = new("SubVote", "#1");
//|         ...
//|         vote.register_consensus(c1, 0);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::register_consensus(vmm_consensus vote,
                                                bit force_through=0);
   vmm_voter voter;
   bit consensus_reached;
   if (this.Xis_sub_consensusX) consensus_reached = this.is_reached();
   if(vote == null) begin
     `vmm_error(this.log,"Cannot register NULL vmm_consensus reference");
     return;
   end
   this.reg_voter_frm_reg_consensus  = 1;
   voter = this.register_voter({"Consensus ",
                                vote.log.get_instance()});
   this.reg_voter_frm_reg_consensus  = 0;
   voter.sub_consensus(vote, force_through);
   if (this.Xis_sub_consensusX && consensus_reached != this.is_reached()) begin
      this.Xparent_voterX.update_vote();
   end
   if (force_through) vote.upward = this;
endfunction: register_consensus


// //////////////////////////////////////////// 
// Function: consensus_force_thru 
// 
// If the force_through argument is TRUE, any consensus forced on the specified sub-consensus
// instance will force the consensus on this vmm_consensus instance. 
// If the force_through argument is FALSE, any consensus forced on the specified sub-consensus
// instance will simply consent to the consensus on this vmm_consensus instance. 
// 
function void vmm_consensus::consensus_force_thru(vmm_consensus vote,
                                                  bit force_through=1);
   bit found = 0;

   if(vote == null) begin
     `vmm_error(this.log,"Cannot force-thru NULL vmm_consensus reference");
     return;
   end

   foreach (this.voters[i]) begin
      if (this.voters[i].get_consensus() == vote) begin
         this.voters[i].force_thru = force_through;
         found = 1;
      end
   end
   if (!found) begin
     `vmm_error(this.log, $psprintf("Cannot force-thru unregistred consensus \"%s\"",
                                    vote.log.get_instance()));
     return;
   end
   vote.upward = (force_through) ? this : null;
   -> vote.new_results;
endfunction: consensus_force_thru


// //////////////////////////////////////////// 
// 
// Task: unregister_consensus 
// 
// Removes a previously registered sub-consensus from this consensus. If the sub-consensus
// was the only participant that objected to the consensus, the consensus will subsequently
// be reached. If the sub-consensus was forcing the consensus despite other objections,
// the consensus will subsequently no longer be reached. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vmm_consensus c1;
//|         c1 = new("SubVote", "#1");
//|         vote.register_consensus(c1, 0);
//|         ...
//|         vote.unregister_consensus(c1);
//|      end
//|   endprogram
function void vmm_consensus::unregister_consensus(vmm_consensus vote);
   foreach (this.voters[i]) begin
      vmm_voter voter = this.voters[i];
      if (voter.get_consensus() == vote) begin
         if (!voter.get_vote()) voter.consent("Dead voter consents by default");
         voter.kill_voter();
         this.voters.delete(i);
         return;
      end
   end
   `vmm_error(this.log, {"Consensus ", vote.log.get_instance(),
                         " is not a registered voter"});
endfunction: unregister_consensus


function void vmm_consensus::unregister_all();
   foreach (this.voters[i]) begin
      vmm_voter voter = this.voters[i];
      voter.kill_voter();
   end
`ifdef VCS2006_06
   // Work-around required by VCS 2006.06
   // but IEEE 1800-2009 compliant
   this.voters.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.voters = '{};
`endif

   this.n_dissenters = 0;
   this.n_forcing    = 0;
`ifdef ENABLE_VMM_CONSENSUS__REACHED
   this.notify.indicate(REACHED);
`endif
endfunction: unregister_all


// //////////////////////////////////////////// 
// 
// Task: wait_for_consensus 
// 
// Waits until all participants, which explicitly consent and none oppose. There can
// be no abstentions. 
// If a consensus is already reached or forced, by the time this task is called, this task
// will return immediately. 
// A consensus may be broken later (if the simulation is still running) by any voter opposing
// the end of test, or a voter forcing the consensus deciding to consent normally or oppose
// normally. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         vote.wait_for_consensus();
//|      end
//|   endprogram
task vmm_consensus::wait_for_consensus();
   wait (this.n_forcing > 0 || this.n_dissenters == 0);
endtask: wait_for_consensus


// //////////////////////////////////////////// 
// 
// Task: wait_for_no_consensus 
// 
// Waits until a consensus is broken by no longer being forced and any one participant opposing.
// If a consensus is not reached, nor forced by the time this task is called, then this task
// will return immediately. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         vote.wait_for_no_consensus();
//|         ...
//|      end
//|   
//|   endprogram
task vmm_consensus::wait_for_no_consensus();
   wait (this.n_forcing == 0 && this.n_dissenters != 0);
endtask: wait_for_no_consensus


// //////////////////////////////////////////// 
// Function: is_reached 
// 
// This method returns an indication, if a consensus is reached. If a consensus exists
// (whether forced or not), a non-zero value is returned. If there is no consensus, and
// the consensus is not being forced, a zero value is returned. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         if (vote.is_reached())
//|   	 `vmm_note (vote.log, "Consensus is reached");
//|         else
//|   	 `vmm_error (vote.log, "Consensus has not reached");
//|         ...
//|      end
//|   
//|   endprogram
function bit vmm_consensus::is_reached();
   return this.n_forcing > 0 || this.n_dissenters == 0;
endfunction: is_reached


// //////////////////////////////////////////// 
// Function: is_forced 
// 
// This method returns an indication, if a participant forces a consensus. If the consensus
// is forced, a non-zero value is returned. If there is no consensus, or the consensus is
// not being forced, a zero value is returned. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         if (vote.is_forced())
//|   	 `vmm_note (vote.log, "Consensus is forced");
//|         end
//|         ...
//|      end
//|   
//|   endprogram
function bit vmm_consensus::is_forced();
   return this.n_forcing > 0;
endfunction: is_forced


// //////////////////////////////////////////// 
// 
// Task: request 
// 
// Makes a request of all currently-opposing participants, in this consensus instance
// that they consent to the consensus. 
// A request is made by indicating the <REQUEST notification on the notify
// notification interface of this consensus instance, and all currently-opposing sub-consensus
// instances. If a request is made on a consensus instance that is a child of a vmm_unit instance,
// the vmm_unit::consensus_requested> method is also invoked. 
// If this consensus forces through to a higher-level consensus, the consensus request
// is propagated upward as well. 
// This task returns when the local consensus is reached. 
// 
task vmm_consensus::request(string        why       = "No reason specified",
                            vmm_consensus requestor = null);
   bit local_opponent = 0;
`ifndef NO_VMM12_PHASING
   vmm_unit req_unit;
`endif

   if (this.upward != null && this.upward != requestor) begin
      fork
         this.upward.request(why, this);
      join_none
   end

   // Trivial request??
   if (this.is_reached()) return;

   // Propagate request to all opposing (sub-consensus)
   foreach (this.voters[i]) begin
      vmm_consensus sub = this.voters[i].get_consensus();
      if (sub != null) begin
         if (sub != requestor && !sub.is_reached()) begin
            // Concurrently request consensus for all opposing sub-consensus
            fork
               sub.request(why, this);
            join_none
         end
         continue;
      end

      if (!this.voters[i].get_vote()) local_opponent = 1;
   end

   // Request consensus of other voters on this one if others are opposing
   if (local_opponent) begin
`ifndef NO_VMM12_PHASING
      vmm_unit req_u, _unit;
`endif
      vmm_object obj;
      this.notify.indicate(vmm_consensus::REQUEST);
      if ($cast(obj, requestor)) begin
         if (obj != null) obj = obj.get_parent();
`ifndef NO_VMM12_PHASING
         void'($cast(req_u, obj));
         $cast(obj, this); // garanteed to work if requestor was succesfully cast
         obj = obj.get_parent();
         if (obj != null && $cast(_unit, obj)) begin
            _unit.consensus_requested(req_u);
         end
`endif
      end
   end

   this.wait_for_consensus();
endtask: request


// //////////////////////////////////////////// 
// Function: psdisplay 
// 
// Returns a human-readable description of the current status of the consensus, and who
// is opposing or forcing the consensus and why. Each line of the description is prefixed
// with the specified prefix. 
// 
//|   
//|   program test_consensus;
//|   
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         $display(vote.psdisplay());
//|         ...
//|      end
//|   
//|   endprogram
function string vmm_consensus::psdisplay(string prefix="");
   $sformat(psdisplay, "%sConsensus %s(%s) is %0s", prefix,
            this.log.get_name(), this.log.get_instance(),
            (this.is_reached() ? (this.is_forced() ? "forced" : "reached")
                               : "NOT reached"));
   if (this.voters.size() == 0) begin
      psdisplay = {psdisplay, " by default"};
   end
   else begin
      foreach (this.voters[i]) begin
         vmm_consensus subvote;
         $sformat(psdisplay, "%s\n%s   %s %0s because %s", psdisplay, prefix,
                  this.voters[i].get_name(),
                  (this.voters[i].get_vote() ?
                   (this.voters[i].get_forced() ? "forces" : "consents")
                   : "opposes"),
                  this.voters[i].get_reason());
         subvote = this.voters[i].get_consensus();
         if (subvote != null) begin
            psdisplay = {psdisplay, "\n", subvote.psdisplay({prefix, "      "})};
         end
      end
   end
endfunction: psdisplay


function void vmm_consensus::yeas(ref string who[],
                                  ref string why[]);
   int n = 0;

   foreach (this.voters[i]) begin
      if (this.voters[i].get_vote()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   foreach (this.voters[i]) begin
      if (this.voters[i].get_vote()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: yeas


// //////////////////////////////////////////// 
// 
// Task: nays 
// 
// Returns a description of the testbench elements, which are currently opposing to the
// end of test, and their respective reasons. 
// 
//|   
//|   program test_consensus;
//|   
//|      string who[];
//|      string why[];
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         vote.nays(who,why);
//|         for(int i=0; i<who.size; i++)
//|            $display(" %s ------ %s",who[i],why[i]);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::nays(ref string who[],
                                  ref string why[]);
   int n = 0;

   foreach (this.voters[i]) begin
      if (!this.voters[i].get_vote()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   foreach (this.voters[i]) begin
      if (!this.voters[i].get_vote()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: nays


// //////////////////////////////////////////// 
// 
// Task: forcing 
// 
// Returns a description of the testbench elements that are currently forcing the end
// of test, and their respective reasons. 
// 
//|   
//|   program test_consensus;
//|   
//|      string who[];
//|      string why[];
//|      vmm_consensus vote = new("Vote", "Main");
//|   
//|      initial begin
//|         ...
//|         vote.forcing(who,why);
//|         for(int i=0; i<who.size; i++)
//|            $display(" %s ------ %s",who[i],why[i]);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_consensus::forcing(ref string who[],
                                     ref string why[]);
   int n = 0;

   foreach (this.voters[i]) begin
      if (this.voters[i].get_vote() &&
          this.voters[i].get_forced()) n++;
   end

   who = new [n];
   why = new [n];

   n = 0;
   foreach (this.voters[i]) begin
      if (this.voters[i].get_vote() &&
          this.voters[i].get_forced()) begin
         who[n] = this.voters[i].get_name();
         why[n] = this.voters[i].get_reason();
         n++;
      end
   end
endfunction: forcing
   
function void vmm_consensus::notify_request();
endfunction:notify_request

function void vmm_consensus::XvoteX(bit was_agree,
                                    bit agree,
                                    bit was_forced,
                                    bit forced);
   if (agree && !was_agree) begin
      this.n_dissenters--;
      if (this.n_dissenters == 0) ->this.new_results;
      this.notify.indicate(NEW_VOTE);
   end
   else if (!agree && was_agree) begin
      if (this.n_dissenters == 0) ->this.new_results;
      this.n_dissenters++;
      this.notify.indicate(NEW_VOTE);
   end

   if (forced && !was_forced) begin
      if (this.n_forcing == 0) ->this.new_results;
      this.n_forcing++;
      this.notify.indicate(NEW_VOTE);
   end
   else if (!forced && was_forced) begin
      this.n_forcing--;
      if (this.n_forcing == 0) ->this.new_results;
      this.notify.indicate(NEW_VOTE);
   end

`ifdef ENABLE_VMM_CONSENSUS__REACHED
   if (this.n_forcing > 0 || this.n_dissenters == 0) this.notify.indicate(REACHED);
   else this.notify.reset(REACHED);
`endif
endfunction: XvoteX

function bit vmm_consensus::is_register_consensus();
  return unit_children_registered;
endfunction

function void vmm_consensus::set_register_consensus();
  unit_children_registered = 1;
endfunction

function vmm_voter::new(string        name,
                        vmm_consensus vote);
   this.name      = name;
   this.consensus = vote;

   this.vote      = 0;
   this.is_forced = 0;
   this.why       = "Opposes by default";

   this.xactor_voter = null;
   this.channel_voter = null;
   this.sub_vote = null;

`ifdef VMM_TR_RECORD
   this.top_stream = vmm_tr_record::open_stream(this.consensus.log.get_instance(), 
                                               "Consensus", vmm_debug::TRACE_SEV);
`endif //VMM_TR_RECORD
endfunction: new


function void vmm_voter::oppose(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 0, this.is_forced, 0);
   end
   this.vote = 0;
   this.is_forced = 0;
   this.why = why;

`ifdef VMM_TR_RECORD
   vmm_tr_record::start_tr(this.top_stream, "[Oppose]", $psprintf("Reason=%s", why));
`endif //VMM_TR_RECORD

endfunction: oppose


function void vmm_voter::consent(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 1, this.is_forced, 0);
   end
   this.vote = 1;
   this.is_forced = 0;
   this.why = why;
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD
endfunction: consent


function void vmm_voter::forced(string why="No reason specified");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 1, this.is_forced, 1);
   end
   this.vote = 1;
   this.is_forced = 1;
   this.why = why;
`ifdef VMM_TR_RECORD
   vmm_tr_record::end_tr(this.top_stream);
`endif //VMM_TR_RECORD
endfunction: forced


task vmm_voter::request(string why = "Consensus requested");
   if (this.consensus != null) begin
      this.consensus.XvoteX(this.vote, 1, this.is_forced, 0);
   end
   this.vote = 1;
   this.is_forced = 0;
   this.why = why;
   if (this.consensus != null) begin
`ifdef VMM_TR_RECORD
      vmm_tr_record::start_tr(this.top_stream, "[Oppose]", $psprintf("Reason=%s", why));
`endif //VMM_TR_RECORD
      this.consensus.request({why, " by ", this.name});
   end
endtask: request


function string vmm_voter::get_name();
   return this.name;
endfunction: get_name


function bit vmm_voter::get_vote();
   return this.vote;
endfunction: get_vote


function bit vmm_voter::get_forced();
   return this.is_forced;
endfunction: get_forced


function string vmm_voter::get_reason();
   return this.why;
endfunction: get_reason


function void vmm_voter::xactor(vmm_xactor xact);
   this.xactor_voter = xact;
   if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
      this.oppose("Transactor is BUSY");
   end
   else this.consent("Transactor is IDLE");
   fork
      begin
         fork
            begin
               // The transactor might have become busy while
               // the forked thread was getting started...
               if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
                  this.oppose("Transactor is BUSY");
               end
               forever begin
                  // Wait for transactor to be IDLE
                  xact.notify.wait_for(vmm_xactor::XACTOR_IDLE);
                  this.consent("Transactor is IDLE");
                  // Prevent an infinite loop
                  if (xact.notify.is_on(vmm_xactor::XACTOR_BUSY)) begin
                     `vmm_fatal(this.xactor_voter.log,
                                "Transactor is indicating both IDLE and BUSY");
                  end
                  // Wait for transactor to be BUSY
                  xact.notify.wait_for(vmm_xactor::XACTOR_BUSY);
                  this.oppose("Transactor is BUSY");
                  // Prevent an infinite loop
                  if (xact.notify.is_on(vmm_xactor::XACTOR_IDLE)) begin
                     `vmm_fatal(this.xactor_voter.log,
                                "Transactor is indicating both IDLE and BUSY");
                  end
               end
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: xactor


function void vmm_voter::channel(vmm_channel chan);
   this.channel_voter = chan;
   if (!chan.notify.is_on(vmm_channel::EMPTY)) begin
      this.oppose("Channel is not empty");
   end
   else this.consent("Channel is empty");
   fork
      begin
         fork
            forever begin
               // Wait for channel to be empty
               chan.notify.wait_for(vmm_channel::EMPTY);
               this.consent("Channel is empty");
               // Wait for channel to be not empty
               chan.notify.wait_for_off(vmm_channel::EMPTY);
               this.oppose("Channel is not empty");
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: channel


function void vmm_voter::notify(vmm_notify ntfy,
                                int notification,
                                bit is_on);
   this.notify_voter = ntfy;
   this.notification = notification;
   if (is_on) begin
      if (!ntfy.is_on(notification)) begin
         this.oppose("Notification is not indicated");
      end
      else this.consent("Notification is indicated");
   end
   else begin
      if (ntfy.is_on(notification)) begin
         this.oppose("Notification is indicated");
      end
      else this.consent("Notification is not indicated");
   end
   fork
      begin
         fork
            if (is_on) begin
               // Check again as it could have change while
               // the thread was forked
               if (!ntfy.is_on(notification)) begin
                  this.oppose("Notification is not indicated");
               end
               else this.consent("Notification is indicated");

               forever begin
                  // Wait for indication
                  ntfy.wait_for(notification);
                  this.consent("Notification is indicated");
                  // Wait for indication to be reset
                  ntfy.wait_for_off(notification);
                  this.oppose("Notification is not indicated");
               end
            end
            if (!is_on) begin
               // Check again as it could have change while
               // the thread was forked
               if (ntfy.is_on(notification)) begin
                  this.oppose("Notification is indicated");
               end
               else this.consent("Notification is not indicated");

               forever begin
                  // Wait for indication
                  ntfy.wait_for_off(notification);
                  this.consent("Notification is not indicated");
                  // Wait for indication to be reset
                  ntfy.wait_for(notification);
                  this.oppose("Notification is indicated");
               end
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: notify


function void vmm_voter::sub_consensus(vmm_consensus vote,
                                       bit force_through);
   this.sub_vote = vote;
   this.force_thru = force_through;
   vote.Xis_sub_consensusX = 1;
   vote.Xparent_voterX = this;

   if (!vote.is_reached()) begin
      this.oppose("Sub-consensus is not reached");
   end
   else this.consent("Sub-consensus is reached");

   fork
      begin
         fork
            forever begin
               this.update_vote();

               // Wait for sub-consensus to reach new results
               @vote.new_results;
            end
         join_none

         @(this.killme);
         disable fork;
      end
   join_none
endfunction: sub_consensus


function void vmm_voter::kill_voter();
   ->this.killme;
   this.consensus = null;
endfunction: kill_voter


function vmm_xactor vmm_voter::get_xactor();
   return this.xactor_voter;
endfunction: get_xactor


function vmm_channel vmm_voter::get_channel();
   return this.channel_voter;
endfunction: get_channel


function vmm_notify vmm_voter::get_notify();
   return this.notify_voter;
endfunction: get_notify


function int vmm_voter::get_notification();
   return this.notification;
endfunction: get_notification


function vmm_consensus vmm_voter::get_consensus();
   return this.sub_vote;
endfunction: get_consensus

function void vmm_voter::update_vote();
   if (this.sub_vote == null) begin
      return;
   end
   if (this.sub_vote.is_forced() && this.force_thru) begin
       this.forced("Sub-consensus forces");
   end
   else if (this.sub_vote.is_reached()) this.consent("Sub-consensus consents");
   else this.oppose("Sub-consensus opposes");

   if (this.consensus && this.consensus.Xis_sub_consensusX) begin
      this.consensus.Xparent_voterX.update_vote();
   end
endfunction: update_vote


`endif // VMM_CONSENSUS__SV
