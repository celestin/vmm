//
// Template for VMM-compliant full-duplex physical-level monitor
// <MON>       Name of monitor transactor
// <IF>        Name of physical interface
// <TR>        Name of input/output transaction descriptor class
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
   virtual function void pre_tx_trans(MON xactor,
                                      TR tr);
   
   endfunction: pre_tx_trans


   // Called at end of observed transaction
   virtual function void post_tx_trans(MON xactor,
                                       TR tr);
   
   endfunction: post_tx_trans


   // Called at start of observed transaction
   virtual function void pre_rx_trans(MON xactor,
                                      TR tr);
   
   endfunction: pre_rx_trans


   // Called at end of observed transaction
   virtual function void post_rx_trans(MON xactor,
                                       TR tr);
   
   endfunction: post_rx_trans
   

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
   virtual task pre_tx_trans(XACT xactor,TR tr);
      fork begin
         vmm_perf_tenure monitor_tx_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(monitor_tx_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(monitor_tx_tenure);
      end join_none
   endtask: pre_tx_trans
   
   //Performace recording for Rx interface of monitor 
   virtual task pre_rx_trans(XACT xactor,TR tr);
      fork begin
         vmm_perf_tenure monitor_rx_tenure= new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(monitor_rx_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(monitor_rx_tenure);
      end join_none
   endtask: pre_rx_trans


endclass: MON_perf_cb
PERF_END

class MON_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: MON_cfg


class MON extends vmm_xactor;

   int OBS_ON_T;
   int OBS_ON_R;
   
   protected MON_cfg cfg;
   local MON_cfg reset_cfg;
   protected TR tx_factory;
   local TR reset_tx_factory;
   protected TR rx_factory;
   local TR reset_rx_factory;
 
   TR_channel tx_chan;
   TR_channel rx_chan;
   virtual IF.passive sigs;
 
   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual IF.passive  sigs,
                       MON_cfg cfg = null,
                       TR_channel tx_chan = null,
                       TR_channel rx_chan = null,
                       TR tx_factory = null,
                       TR rx_factory = null);
   
   MACRO_START
   `vmm_xactor_member_begin(MON)
     `vmm_xactor_member_scalar(OBS_ON_T, DO_ALL)
     `vmm_xactor_member_scalar(OBS_ON_R, DO_ALL)
     `vmm_xactor_member_channel(tx_chan,  DO_ALL)
     `vmm_xactor_member_channel(rx_chan,  DO_ALL)
     //ToDo: Add vmm xactor member
 
   `vmm_xactor_member_end(MON)
   
   //ToDo: Add required short hand override method
 
   MACRO_END
   extern virtual function void reconfigure(MON_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   extern protected virtual task main();
   extern protected virtual task tx_monitor();
   extern protected virtual task rx_monitor();

endclass: MON

function MON::new(string inst = "",
                  int stream_id = -1,
                  virtual IF.passive  sigs,
                  MON_cfg cfg = null,
                  TR_channel tx_chan = null,
                  TR_channel rx_chan = null,
                  TR tx_factory = null,
                  TR rx_factory = null);

   super.new("MON Transactor", inst, stream_id);

   this.OBS_ON_T = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBS_ON_R = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (tx_chan == null) tx_chan = new("MON Tx Channel", inst);
   this.tx_chan = tx_chan;
   if (rx_chan == null) rx_chan = new("MON Rx Channel", inst);
   this.rx_chan = rx_chan;

   if (tx_factory == null) tx_factory = new;
   this.tx_factory = tx_factory;
   this.reset_tx_factory = tx_factory;

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

   this.tx_chan.flush();
   this.rx_chan.flush();

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
      this.tx_factory = this.reset_tx_factory;
      this.rx_factory = this.reset_rx_factory;
   end

endfunction: reset_xactor


NORMAL_END
task MON::main();
   super.main();

   fork
      tx_monitor();
      rx_monitor();
   join
endtask: main


task MON::tx_monitor();

   forever begin
      TR tr;

      // ToDo: Wait for start of transaction

      $cast(tr, this.tx_factory.copy());
      `vmm_callback(MON_callbacks,
                    pre_tx_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBS_ON_T, tr);

      `vmm_trace(this.log, "Starting Tx transaction...");

      // ToDo: Observe transaction

      `vmm_trace(this.log, "Completed Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBS_ON_T);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(MON_callbacks,
                    post_tx_trans(this, tr));
      SCB_INT_MTHD_TWO_START
      this.exp_vmm_sb_ds(tr);
      SCB_INT_MTHD_TWO_END

      this.tx_chan.sneak(tr);
   end

endtask: tx_monitor


task MON::rx_monitor();

   forever begin
      TR tr;

      // ToDo: Wait for start of transaction

      $cast(tr, this.rx_factory.copy());
      `vmm_callback(MON_callbacks,
                    pre_rx_trans(this, tr));

      tr.notify.indicate(vmm_data::STARTED);
      this.notify.indicate(this.OBS_ON_R, tr);

      `vmm_trace(this.log, "Starting Rx transaction...");

      // ToDo: Observe transaction

      `vmm_trace(this.log, "Completed Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.notify.reset(this.OBS_ON_R);
      tr.notify.indicate(vmm_data::ENDED);

      `vmm_callback(MON_callbacks,
                    post_rx_trans(this, tr));
      SCB_INT_MTHD_TWO_START
      this.exp_vmm_sb_ds(tr);
      SCB_INT_MTHD_TWO_END

      this.rx_chan.sneak(tr);
   end

endtask: rx_monitor

`endif // MON__SV
