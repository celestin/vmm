//
// Template for VMM-compliant half-duplex physical-level monitor
// <MON>        Name of monitor transactor
// <IF>         Name of physical interface
// <TR>         Name of output transaction descriptor class
//

`ifndef MON__SV
`define MON__SV

`include "IF.sv"
`include "TR.sv"

typedef class MON;

class MON_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use a task if callbacks can be blocking

   // Called at start of observed transaction
   virtual function void pre_trans(MON xactor,
                                   TR tr);
   
   endfunction: pre_trans


   // Called before acknowledging a transaction
   virtual function pre_ack(MON xactor,
                            TR tr);
   
   endfunction: pre_ack
   

   // Called at end of observed transaction
   virtual function void post_trans(MON xactor,
                                    TR tr);
   
   endfunction: post_trans
   
   // Callback method post_cb_trans can be used for coverage
   virtual task post_cb_trans(MON xactor,
                              TR tr);
   
   endtask: post_cb_trans

endclass: MON_callbacks
PERF_START


class MON_perf_cb extends vmm_xactor_callbacks;

   vmm_perf_analyzer perf;

   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction:new

   //Performace recording for Tx interface of monitor 
   virtual task pre_trans(XACT xactor,TR tr);
      fork begin
         vmm_perf_tenure monitor_tx_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(monitor_tx_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(monitor_tx_tenure);
      end join_none
   endtask: pre_trans
   
endclass: MON_perf_cb
PERF_END


class MON_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: MON_cfg


class MON extends vmm_xactor;

   int OBSERVING;
   
   protected MON_cfg cfg;
   local MON_cfg reset_cfg;
   protected TR rx_factory;
   local TR reset_rx_factory;

   TR_channel out_chan;
   virtual IF.slave sigs;

   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual IF.slave sigs,
                       MON_cfg cfg = null,
                       TR_channel out_chan = null,
                       TR rx_factory = null);

   MACRO_START
   `vmm_xactor_member_begin(MON)
     `vmm_xactor_member_scalar(OBSERVING, DO_ALL)
     `vmm_xactor_member_channel(out_chan, DO_ALL)
     // ToDo: Add vmm xactor member

   `vmm_xactor_member_end(MON)
   // ToDo: Add required short hand override method

   MACRO_END
   extern virtual function void reconfigure(MON_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   extern protected virtual task main();

endclass: MON


function MON::new(string inst = "",
                  int stream_id = -1,
                  virtual IF.slave  sigs,
                  MON_cfg cfg = null,
                  TR_channel out_chan = null,
                  TR rx_factory = null);

   super.new("MON Transactor", inst, stream_id);

   this.OBSERVING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (out_chan == null) out_chan = new("MON Output Channel", inst);
   this.out_chan = out_chan;

   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;

endfunction: new


function void MON::reconfigure(MON_cfg cfg);

   if (!this.notify.is_on(XACTOR_IDLE)) begin
      `vmm_warning(this.log, "Transactor should be reconfigured only when IDLE");
   end

   this.cfg = cfg;
   
   // ToDo: Notify any running threads of the new configuration
endfunction: reconfigure


NORMAL_START
function void MON::reset_xactor(reset_e rst_typ = SOFT_RST);

   super.reset_xactor(rst_typ);

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
task MON::main();
   super.main();

   forever begin
      TR tr;

      // ToDo: Wait for start of transaction

      $cast(tr, this.rx_factory.copy());
      `vmm_callback(MON_callbacks,
                    pre_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBSERVING, tr);

      `vmm_trace(this.log, "Starting transaction...");

      // ToDo: Observe first half of transaction
      // ToDo: User need to add monitoring logic and remove "#0;"

      #0;
      `vmm_note(this.log," User need to add monitoring logic "); 
      tr.status = TR::IS_OK;
      `vmm_callback(MON_callbacks,
                    pre_ack(this, tr));

      // ToDo: React to observed transaction with ACK/NAK

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBSERVING);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(MON_callbacks,
                    post_trans(this, tr));
      SCB_INT_MTHD_TWO_START
      this.exp_vmm_sb_ds(tr);
      SCB_INT_MTHD_TWO_END

      this.out_chan.sneak(tr);
   end

endtask: main

`endif // MON__SV
