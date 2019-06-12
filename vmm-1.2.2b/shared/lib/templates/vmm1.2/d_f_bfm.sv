//
// Template for VMM-compliant full-duplex physical-level transactor
// <XACT>       Name of transactor
// <IF>         Name of physical interface
// <PRT>       Name of the interface wrapper object
// <TR>         Name of input/output transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "IF.sv"
`include "TR.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

   `vmm_typename(XACT_callbacks)
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

   `vmm_typename(XACT_perf_cb)
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

   `vmm_typename(XACT_cfg)
   // ToDo: Add transactor configuration class properties
  
   rand int mode;

endclass: XACT_cfg


class XACT extends vmm_xactor;

   `vmm_typename(XACT)
   int EXECUTING;
   int OBSERVING;
   
   protected XACT_cfg cfg;
   local XACT_cfg reset_cfg;
   protected TR rx_factory;
   local TR reset_rx_factory;
   TR_channel in_chan;
   TR_channel out_chan;
   RTLCFG_START
   XACT_config rtl_cfg;  //Instance of RTL config
   RTLCFG_END
   DRIV_TLM_B_TRANS_EX_START
   vmm_tlm_b_transport_export #(XACT,TR) drv_b_export;    //Uni directional blocking
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
   vmm_tlm_nb_transport_fw_export #(XACT,TR) drv_nb_export;  //Uni directional non-blocking
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_NB_TRANS_EX_START
   vmm_tlm_nb_transport_export #(XACT,TR) drv_nb_bidir;     //Bi-directional non-blocking    
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
   vmm_tlm_target_socket#(XACT,TR) drv_target_exp;          //Bi-directional blocking and non-blocking
   DRIV_TLM_SMPL_TRGT_SCKT_END
   PRT iport_obj;
   virtual IF.master sigs;

   extern function new(string name = "XACT",
                       string inst = "",
                       int stream_id = -1,
                       vmm_object parent = null,
                       XACT_cfg cfg = null,
                       DRIV_CHNL_START
                       TR_channel in_chan = null,
                       TR_channel out_chan = null,
                       DRIV_CHNL_END
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
   XCT_IMPL_START
   RTLCFG_START
   extern virtual function void configure_ph();
   RTLCFG_END
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task start_ph();
   XCT_IMPL_END
   XCT_EXPL_START
   extern virtual task main();
   extern function void connect();
   XCT_EXPL_END
   extern protected virtual task tx_driver();
   extern protected virtual task rx_monitor();
   DRIV_TLM_B_TRANS_EX_START
   extern task b_transport(int id=-1, TR trans, int delay);
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
   extern task b_transport(int id=-1, TR trans, int delay);
   DRIV_TLM_SMPL_TRGT_SCKT_END
   DRIV_TLM_NB_TRANS_EX_START
   extern function vmm_tlm::sync_e nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
   extern function vmm_tlm::sync_e nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
   extern function vmm_tlm::sync_e nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   DRIV_TLM_SMPL_TRGT_SCKT_END

endclass: XACT


function XACT::new(string name = "XACT",
                   string inst = "",
                   int stream_id = -1,
                   vmm_object parent =  null,
                   XACT_cfg cfg = null,
                   DRIV_CHNL_START
                   TR_channel in_chan = null,
                   TR_channel out_chan = null,
                   DRIV_CHNL_END
                   TR rx_factory = null);

   super.new(name, inst, stream_id, parent);
   this.EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBSERVING = this.notify.configure(-1, vmm_notify::ON_OFF);
   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;
   if (in_chan == null) in_chan = new("XACT Input Channel", "in_chan");
   if (out_chan == null) out_chan = new("XACT Output Channel", "out_chan");
   DRIV_CHNL_START
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);
   this.out_chan = out_chan;
   DRIV_CHNL_END
   DRIV_TLM_B_TRANS_EX_START
   drv_b_export = new(this,"Driver blocking export");
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
   drv_nb_export = new(this,"Driver non-blocking export");
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_NB_TRANS_EX_START
   drv_nb_bidir = new(this,"Driver non-blocking bi-dir export");
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
   drv_target_exp = new(this,"Driver target socket");
   DRIV_TLM_SMPL_TRGT_SCKT_END
   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;
   XCT_EXPL_START
   //If explicit transactor, then attempt to get the interface wrapper from constructor
   this.connect();
   XCT_EXPL_END
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
XCT_IMPL_START
RTLCFG_START


function void XACT::configure_ph();
   $cast(rtl_cfg, vmm_rtl_config::get_config(this, `__FILE__, `__LINE__));
   if (rtl_cfg == null) begin
      `vmm_error(log, `vmm_sformatf("null Config obtained for %s", this.get_object_hiername()));
      return;
   end
endfunction: configure_ph
RTLCFG_END
XCT_IMPL_END
XCT_IMPL_START


function void XACT::connect_ph();
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"drv_port"))) begin
      if (iport_obj != null)
         this.sigs = iport_obj.iport_mst;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction: connect_ph
XCT_IMPL_END
XCT_IMPL_START


function void XACT::start_of_sim_ph();
   if (sigs == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction: start_of_sim_ph
XCT_IMPL_END
XCT_IMPL_START


task XACT::start_ph();
   super.start_ph();
   fork 
      tx_driver();
      rx_monitor();
   join_none
endtask: start_ph
XCT_IMPL_END
XCT_EXPL_START


task XACT::main();
   super.main();
   fork 
      tx_driver();
      rx_monitor();
   join_none
endtask: main
XCT_EXPL_END
XCT_EXPL_START


function void XACT::connect();
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"drv_port"))) begin
      if (iport_obj != null)
         this.sigs = iport_obj.iport_mst;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction: connect
XCT_EXPL_END


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
      `vmm_trace(this.log, "Starting Tx transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));
      tr.notify.indicate(vmm_data::STARTED);
      
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
DRIV_TLM_B_TRANS_EX_START


task XACT::b_transport(int id=-1, TR trans, int delay);
   `vmm_note(log, "transaction received from the generator");
   in_chan.put(trans);
endtask: b_transport
DRIV_TLM_B_TRANS_EX_END
DRIV_TLM_SMPL_TRGT_SCKT_START


task XACT::b_transport(int id=-1, TR trans, int delay);
   `vmm_note(log, "transaction received from the generator");
   in_chan.put(trans);
endtask: b_transport
DRIV_TLM_SMPL_TRGT_SCKT_END
DRIV_TLM_NB_TRANS_FW_EX_START


function vmm_tlm::sync_e XACT::nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   `vmm_note(log, "SOCKET target transaction received from the generator");
   in_chan.sneak(trans);
endfunction: nb_transport_fw
DRIV_TLM_NB_TRANS_FW_EX_END
DRIV_TLM_NB_TRANS_EX_START


function vmm_tlm::sync_e XACT::nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   `vmm_note(log, "SOCKET target transaction received from the generator");
   in_chan.sneak(trans);
endfunction: nb_transport_fw
DRIV_TLM_NB_TRANS_EX_END
DRIV_TLM_SMPL_TRGT_SCKT_START


function vmm_tlm::sync_e XACT::nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
   `vmm_note(log, "SOCKET target transaction received from the generator");
   in_chan.sneak(trans);
endfunction: nb_transport_fw
DRIV_TLM_SMPL_TRGT_SCKT_END

`endif // XACT__SV
