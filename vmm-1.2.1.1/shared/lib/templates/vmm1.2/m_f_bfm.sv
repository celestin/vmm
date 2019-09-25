//
// Template for VMM-compliant full-duplex physical-level monitor
// <MON>       Name of monitor transactor
// <IF>        Name of physical interface
// <PRT>      Name of the interface wrapper object
// <TR>        Name of input/output transaction descriptor class
//
 
`ifndef MON__SV
`define MON__SV

`include "IF.sv"
`include "TR.sv"

typedef class MON;

class MON_callbacks extends vmm_xactor_callbacks;

   `vmm_typename(MON_callbacks)
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

   `vmm_typename(MON_perf_cb)
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
MNTR_OBS_MTHD_THREE_START


class MON_to_subscribers_cb extends vmm_notify_callbacks;

   `vmm_typename(MON_to_subscribers_cb)
   vmm_tlm_analysis_port #(MON_to_subscribers_cb,TR) mon2sub_analys_port;
   function new();
      mon2sub_analys_port = new(this,"analys_port");
   endfunction: new
   

   virtual function void indicated(vmm_data status);
      TR tr;
      $cast(tr,status);
      mon2sub_analys_port.write(tr);
   endfunction: indicated

endclass: MON_to_subscribers_cb
MNTR_OBS_MTHD_THREE_END


class MON_cfg;

   `vmm_typename(MON_cfg)
   // ToDo: Add transactor configuration class properties

   rand int mode;

endclass: MON_cfg


class MON extends vmm_xactor;

   `vmm_typename(MON)
   int OBS_ON_T;
   int OBS_ON_R;
   
   protected MON_cfg cfg;
   local MON_cfg reset_cfg;
   protected TR tx_factory;
   local TR reset_tx_factory;
   protected TR rx_factory;
   local TR reset_rx_factory;
   MNTR_OBS_MTHD_TWO_START
   vmm_tlm_analysis_port #(MON,TR) mon_analysis_port;  //TLM analysis port
   MNTR_OBS_MTHD_TWO_END
   PRT iport_obj;
   virtual IF.passive sigs;
   MNTR_OBS_MTHD_ONE_START 
   TR_channel tx_chan;
   TR_channel rx_chan;
   MNTR_OBS_MTHD_ONE_END
   MNTR_OBS_MTHD_FOUR_START
   int TRANS_START;
   MNTR_OBS_MTHD_FOUR_END
   MNTR_OBS_MTHD_THREE_START
   int TRANS_START;
   MNTR_OBS_MTHD_THREE_END
   //ToDo: Add another class property if required
 
   extern function new(string name="MON",
                       string inst = "",
                       int stream_id = -1,
                       vmm_object parent, 
                       MON_cfg cfg = null,
                       MNTR_OBS_MTHD_ONE_START
                       TR_channel tx_chan = null,
                       TR_channel rx_chan = null,
                       MNTR_OBS_MTHD_ONE_END
                       TR tx_factory = null,
                       TR rx_factory = null);
   
   MACRO_START
   `vmm_xactor_member_begin(MON)
      `vmm_xactor_member_scalar(OBS_ON_T, DO_ALL)
      `vmm_xactor_member_scalar(OBS_ON_R, DO_ALL)
      MNTR_OBS_MTHD_ONE_START
      `vmm_xactor_member_channel(tx_chan,  DO_ALL)
      `vmm_xactor_member_channel(rx_chan,  DO_ALL)
      MNTR_OBS_MTHD_ONE_END
       //ToDo: Add vmm xactor member if any class property added later

   `vmm_xactor_member_end(MON)
   //ToDo: Add required short hand override method

   MACRO_END
   extern virtual function void reconfigure(MON_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   XCT_IMPL_START
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task start_ph();
   XCT_IMPL_END
   XCT_EXPL_START
   extern virtual task main();
   extern virtual function void connect();
   XCT_EXPL_END
   extern protected virtual task tx_monitor();
   extern protected virtual task rx_monitor();

endclass: MON


function MON::new(string name="MON",
                  string inst = "",
                  int stream_id = -1,
                  vmm_object parent,
                  MON_cfg cfg = null,
                  MNTR_OBS_MTHD_ONE_START 
                  TR_channel tx_chan = null,
                  TR_channel rx_chan = null,
                  MNTR_OBS_MTHD_ONE_END
                  TR tx_factory = null,
                  TR rx_factory = null);

   super.new(name, inst, stream_id, parent);
   this.OBS_ON_T = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBS_ON_R = this.notify.configure(-1, vmm_notify::ON_OFF);
   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;
   MNTR_OBS_MTHD_TWO_START
   mon_analysis_port = new (this,"mon_analysis_port");
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_ONE_START
   if (tx_chan == null) tx_chan = new("MON Tx Channel", inst);
   this.tx_chan = tx_chan;
   if (rx_chan == null) rx_chan = new("MON Rx Channel", inst);
   this.rx_chan = rx_chan;
   MNTR_OBS_MTHD_ONE_END
   if (tx_factory == null) tx_factory = new;
   this.tx_factory = tx_factory;
   this.reset_tx_factory = tx_factory;
   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;
   MNTR_OBS_MTHD_THREE_START
   this.TRANS_START = this.notify.configure(-1);
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START
   this.TRANS_START = this.notify.configure(-1);
   MNTR_OBS_MTHD_FOUR_END
   XCT_EXPL_START
   //If explicit transactor, then attempt to get the interface wrapper from constructor
   this.connect();
   XCT_EXPL_END
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
   MNTR_OBS_MTHD_ONE_START
   this.tx_chan.flush();
   this.rx_chan.flush();
   MNTR_OBS_MTHD_ONE_END
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
XCT_IMPL_START


function void MON::connect_ph();
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"mon_port"))) begin
      if (iport_obj != null)
         this.sigs = iport_obj.iport_mon;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction: connect_ph
XCT_IMPL_END
XCT_IMPL_START


function void MON::start_of_sim_ph();
  if (iport_obj == null)
     `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction: start_of_sim_ph
XCT_IMPL_END
XCT_IMPL_START


task MON::start_ph();
   super.start_ph();
   fork
      tx_monitor();
      rx_monitor();
   join_none
endtask: start_ph
XCT_IMPL_END
XCT_EXPL_START


task MON::main();
   super.main();
   fork
      tx_monitor();
      rx_monitor();
   join_none
endtask: main
XCT_EXPL_END
XCT_EXPL_START


function void MON::connect();
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"mon_port"))) begin
      if (iport_obj != null)
         this.sigs = iport_obj.iport_mon;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction: connect
XCT_EXPL_END


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
      MNTR_OBS_MTHD_TWO_START
      mon_analysis_port.write(tr);
      MNTR_OBS_MTHD_TWO_END
      MNTR_OBS_MTHD_ONE_START 
      this.tx_chan.sneak(tr);
      MNTR_OBS_MTHD_ONE_END
      MNTR_OBS_MTHD_FOUR_START
      this.notify.indicate(this.TRANS_START, tr);
      MNTR_OBS_MTHD_FOUR_END
      MNTR_OBS_MTHD_THREE_START
      this.notify.indicate(this.TRANS_START, tr);
      MNTR_OBS_MTHD_THREE_END
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
      MNTR_OBS_MTHD_ONE_START 
      this.rx_chan.sneak(tr);
      MNTR_OBS_MTHD_ONE_END
   end
endtask: rx_monitor


`endif // MON__SV
