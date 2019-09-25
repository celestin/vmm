//
// Template for VMM-compliant full-duplex physical-level transactor
// <XACT>       Name of transactor
// <IF>         Name of physical interface
// <TR>         Name of input/output transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "IF.sv"
`include "TR.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

   // ToDo: Add additional relevant callbacks
   // ToDo: Use task if callbacks can be blocking

   // Called before a transaction is executed
   virtual task pre_ex_trans(XACT xactor,
                             TR tr,
                             ref bit drop);
   
   endtask: pre_ex_trans


   // Called after a transaction has been executed
   virtual task post_ex_trans(XACT xactor,
                              TR tr);
   
   endtask: post_ex_trans


   // Called at start of observed transaction
   virtual function void pre_obs_trans(XACT xactor,
                                       TR tr);
                          
   endfunction: pre_obs_trans


   // Called before acknowledging a transaction
   virtual function void pre_ack(XACT xactor,
                                 TR tr);
   
   endfunction: pre_ack


   // Called at end of observed transaction
   virtual function void post_obs_trans(XACT xactor,
                                        TR tr);
   
   endfunction: post_obs_trans

endclass: XACT_callbacks

PERF_START
class XACT_perf_cb extends vmm_xactor_callbacks;

   vmm_perf_analyzer perf;
  
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction:new
  
  //Performace recording for Driving channel (Execute) of driver 
   virtual task pre_ex_trans(XACT xactor,TR tr,ref bit drop);
      fork begin
         vmm_perf_tenure driver_ex_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(driver_ex_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(driver_ex_tenure);
      end join_none
   endtask: pre_ex_trans 
   
   //Performace recording for Receiveing channel (Observe) of driver 
   virtual task pre_obs_trans(XACT xactor,TR tr);
      fork begin
         vmm_perf_tenure driver_obs_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(driver_obs_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(driver_obs_tenure);
      end join_none
   endtask: pre_obs_trans
  
endclass: XACT_perf_cb
PERF_END

class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: XACT_cfg


class XACT extends vmm_xactor;

   int EXECUTING;
   int OBSERVING;
   
   protected XACT_cfg cfg;
   local XACT_cfg reset_cfg;
   protected TR rx_factory;
   local TR reset_rx_factory;

   TR_channel in_chan;
   TR_channel out_chan;
   virtual IF.master sigs;

   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual IF.master sigs,
                       XACT_cfg cfg = null,
                       TR_channel in_chan = null,
                       TR_channel out_chan = null,
                       TR rx_factory = null);
   
   MACRO_START
   `vmm_xactor_member_begin(XACT)
     `vmm_xactor_member_scalar(EXECUTING, DO_ALL)
     `vmm_xactor_member_scalar(OBSERVING, DO_ALL)
     `vmm_xactor_member_channel(in_chan, DO_ALL)
     `vmm_xactor_member_channel(out_chan, DO_ALL)
     // ToDo: Add vmm xactor member

   `vmm_xactor_member_end(XACT)
   // ToDo: Add required short hand override method

   MACRO_END
   extern virtual function void reconfigure(XACT_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   extern protected virtual task main();
   extern protected virtual task tx_driver();
   extern protected virtual task rx_monitor();

endclass: XACT


function XACT::new(string inst = "",
                   int stream_id = -1,
                   virtual IF.master sigs,
                   XACT_cfg cfg = null,
                   TR_channel in_chan = null,
                   TR_channel out_chan = null,
                   TR rx_factory = null);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBSERVING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);

   if (out_chan == null) out_chan = new("XACT Output Channel", inst);
   this.out_chan = out_chan;

   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;

endfunction: new


function void XACT::reconfigure(XACT_cfg cfg);

   if (!this.notify.is_on(XACTOR_IDLE)) begin
      `vmm_warning(this.log, "Transactor should be reconfigured only when IDLE");
   end

   this.cfg = cfg;   
   // ToDo: Notify any running threads of the new configuration

endfunction: reconfigure


NORMAL_START
function void XACT::reset_xactor(reset_e rst_typ = SOFT_RST);

   super.reset_xactor(rst_typ);

   // ToDo: Reset output/inout signals
   this.sigs.mck1.sync_txd <= 0;
   this.sigs.mck1.sync_dat <= 'z;
   this.sigs.async_en      <= 0;

   this.in_chan.flush();
   this.out_chan.flush();

   // ToDo: Reset other state information

   if (rst_typ != SOFT_RST) begin
      // ToDo: Reset state if FIRM or above
   end

   if (rst_typ == PROTOCOL_RST) begin
      // ToDo: Reset state if PROTOCOL
   end
   
   if (rst_typ == HARD_RST) begin
      // ToDo: Reset state if HARD or above
      this.cfg = this.reset_cfg;
      this.rx_factory = this.reset_rx_factory;
   end

endfunction: reset_xactor


NORMAL_END
task XACT::main();
   super.main();

   fork
      tx_driver();
      rx_monitor();
   join
endtask: main


task XACT::tx_driver();

   forever begin
      TR tr;
      bit drop;

      // ToDo: Set output/inout signals to their idle state
      this.sigs.mck1.sync_txd <= 0;
      this.sigs.async_en      <= 0;
   
      this.wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    pre_ex_trans(this, tr, drop));
      if (drop) begin
         void'(this.in_chan.remove());
         continue;
      end
   
      void'(this.in_chan.start());
      this.notify.indicate(this.EXECUTING, tr);

      tr.notify.indicate(vmm_data::STARTED);
      `vmm_trace(this.log, "Starting Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      case (tr.kind) 
         TR::READ: begin
            // ToDo: Implement READ transaction
         end

         TR::WRITE: begin
            // ToDo: Implement WRITE transaction
         end
      endcase
        // ToDo: User need to add driving logic and remove $finish;"
     `vmm_note(log, "User need to add driving logic and remove $finish");
      $finish;
      `vmm_note(this.log," User need to add driving logic ");
      this.notify.reset(this.EXECUTING);
      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(XACT_callbacks,
                    post_ex_trans(this, tr));
   
      void'(this.in_chan.remove());
   end

endtask: tx_driver

task XACT::rx_monitor();

   forever begin
      TR tr;

      // ToDo: Set output signals to their idle state
      this.sigs.mck1.sync_dat <= 'z;
   
      // ToDo: Wait for start of transaction

      $cast(tr, this.rx_factory.copy());
      `vmm_callback(XACT_callbacks,
                    pre_obs_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBSERVING, tr);

      `vmm_trace(this.log, "Starting Rx transaction...");

      // ToDo: Observe first half of transaction
      // ToDo: User need to add monitoring logic and remove $finish;"
     `vmm_note(log, "User need to add monitoring logic and remove $finish");
      $finish;
      tr.status = TR::IS_OK;
      `vmm_callback(XACT_callbacks,
                    pre_ack(this, tr));

      // ToDo: React to observed transaction with ACK/NAK

      `vmm_trace(this.log, "Completed Rx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBSERVING);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(XACT_callbacks,
                    post_obs_trans(this, tr));
      this.out_chan.sneak(tr);
   end

endtask: rx_monitor

`endif // XACT__SV
