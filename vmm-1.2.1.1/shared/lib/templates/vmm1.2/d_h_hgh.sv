//
// Template for VMM-compliant half-duplex functional-level transactor
// <XACT>       Name of transactor
// <TR>         Name of high-level transaction descriptor class
// <TX>         Name of low-level transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "TR.sv"
`include "TX.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

   `vmm_typename(XACT_callbacks)
   // ToDo: Add additional relevant callbacks
   // ToDo: Use a task if callbacks can be blocking

   // Called before a transaction is executed
   virtual function void pre_trans(XACT xactor,
                                   TR tr,
                                   ref bit drop);
   endfunction: pre_trans


   virtual function void pre_trans_exec(XACT xactor,
                                        TR tr,
                                        TX tx[$]);
   endfunction: pre_trans_exec


   // Called at start of lower transaction
   virtual task pre_exec(XACT xactor,
                         TX tr,
                         bit drop);
   endtask: pre_exec

   
   // Called at end of lower transaction
   virtual task post_exec(XACT xactor,
                          TX tr);
   endtask: post_exec

   
   virtual function post_trans_exec(XACT xactor,
                                    TR tr,
                                    TX tx[$]);
   endfunction: post_trans_exec

   
   // Called after a transaction has been executed
   virtual function void post_trans(XACT xactor,
                                    TR tr);
   endfunction: post_trans

endclass: XACT_callbacks

PERF_START
class XACT_perf_cb extends vmm_xactor_callbacks;

   `vmm_typename(XACT_perf_cb)
   vmm_perf_analyzer perf;
  
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction:new
   // ToDo: Add required parametes in post_send
   virtual task post_send();
      fork begin
         vmm_perf_tenure driver_tenure = new();

         // ToDo: Add tenure start notification in wait_for(). 
         //Example:obj.notify.wait_for(. . .);

         this.perf.start_tenure(driver_tenure);

         // ToDo: Add tenure start notification in wait_for().
         //Example:obj.notify.wait_for(. . .);

         this.perf.end_tenure(driver_tenure);

      end join_none
   endtask: post_send

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
   int SUB_EXECUTING;
   
   protected XACT_cfg cfg;
   local XACT_cfg reset_cfg;

   TR_channel in_chan;
   TX_channel exec_chan;
   DRIV_TLM_B_TRANS_EX_START
   vmm_tlm_b_transport_export #(XACT,TR)     drv_b_export;   //Uni directional blocking
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
   vmm_tlm_nb_transport_fw_export #(XACT,TR) drv_nb_export;  //Uni directional non-blocking
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_NB_TRANS_EX_START
   vmm_tlm_nb_transport_export #(XACT,TR)    drv_nb_bidir;   //Bi-directional non-blocking    
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
   vmm_tlm_target_socket#(XACT,TR)           drv_target_exp; //Bi-directional blocking and non-blocking
   DRIV_TLM_SMPL_TRGT_SCKT_END
 
   extern function new(string name = "XACT",
                       string inst = "",
                       int stream_id = -1,
                       vmm_object parent = null,
                       XACT_cfg cfg = null,
                       DRIV_CHNL_START
                       TR_channel in_chan = null,
                       TX_channel exec_chan = null
                       DRIV_CHNL_END
                      );

   MACRO_START
   `vmm_xactor_member_begin(XACT)
     `vmm_xactor_member_scalar(EXECUTING, DO_ALL)
     `vmm_xactor_member_scalar(SUB_EXECUTING, DO_ALL)
     `vmm_xactor_member_channel(in_chan, DO_ALL)
     `vmm_xactor_member_channel(exec_chan,   DO_ALL)
     // ToDo: Add vmm xactor members

   `vmm_xactor_member_end(XACT)
   
   // ToDo: Add required short hand override method

   MACRO_END
   extern virtual function void reconfigure(XACT_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   XCT_IMPL_START
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task start_ph();
   extern virtual task run_ph();
   XCT_IMPL_END
   XCT_EXPL_START
   extern virtual task main();
   extern function void connect();
   XCT_EXPL_END
   extern protected virtual task tx_driver();
   extern task b_transport(int id=-1, TR trans, int delay);
   extern function vmm_tlm::sync_e nb_transport_fw(int id=-1, TR trans, ref vmm_tlm::phase_e ph, int delay);
 
endclass: XACT


function XACT::new(string name ="XACT",
                   string inst = "",
                   int stream_id = -1,
                   vmm_object parent = null,
                   XACT_cfg cfg = null,
                   DRIV_CHNL_START
                   TR_channel in_chan = null,
                   TX_channel exec_chan = null
                   DRIV_CHNL_END
                   );

   super.new(name inst, stream_id, parent);

   this.EXECUTING     = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.SUB_EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   if (exec_chan == null) exec_chan = new("XACT Execution Channel", inst);
   DRIV_CHNL_START 
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);
   this.exec_chan = exec_chan;
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

   this.in_chan.flush();
   this.exec_chan.flush();

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
   end
endfunction: reset_xactor


NORMAL_END
XCT_EXPL_START
task XACT::main(); 
  super.main();
  fork 
      tx_driver();
  join
endtask: main
XCT_EXPL_END
XCT_EXPL_START


function void XACT::connect();
//ToDo:Add the components to connect

endfunction: connect
XCT_EXPL_END
XCT_IMPL_START


function void XACT::connect_ph();
endfunction: connect_ph
XCT_IMPL_END
XCT_IMPL_START


function void XACT::start_of_sim_ph();
endfunction: start_of_sim_ph
XCT_IMPL_END
XCT_IMPL_START


task XACT::start_ph();
   super.start_ph();
   fork
      tx_driver();
   join_none
endtask: start_ph
XCT_IMPL_END
XCT_IMPL_START


task XACT::run_ph();
endtask: run_ph
XCT_IMPL_END


task XACT::tx_driver();

   forever begin
      TR tr;
      TX tx[$];
      bit drop;

      this.wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    pre_trans(this, tr, drop));
      if (drop) begin
         void'(this.in_chan.remove());
         continue;
      end
   
      void'(this.in_chan.start());
      this.notify.indicate(this.EXECUTING, tr);

      `vmm_trace(this.log, "Starting transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      // ToDo: Turn high-level transaction into a series of
      //       low-level transactions

      `vmm_callback(XACT_callbacks,
                    pre_trans_exec(this, tr, tx));

      foreach (tx[i]) begin
         drop = 0;
         `vmm_callback(XACT_callbacks,
                       pre_exec(this, tx[i], drop));
         if (drop) continue;

         this.notify.indicate(this.SUB_EXECUTING, tx[i]);

         `vmm_debug(this.log, "Executing lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         
         this.exec_chan.put(tx[i]);

         // ToDo: Add completion model if not blocking
         
         this.notify.reset(this.SUB_EXECUTING);

         `vmm_debug(this.log, "Executed lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         
         `vmm_callback(XACT_callbacks,
                       post_exec(this, tx[i]));
      end

      `vmm_callback(XACT_callbacks,
                    post_trans_exec(this, tr, tx));

      // ToDo: Determine result of high-level transaction from the
      //       results of the low-level transactions

      this.notify.reset(this.EXECUTING);
      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      `vmm_callback(XACT_callbacks,
                    post_trans(this, tr));
   
      void'(this.in_chan.remove());
   end

endtask: tx_driver


task XACT::b_transport(int id=-1, TR trans, int delay);
   `vmm_note(log, "transaction received from the generator");
   in_chan.put(trans);
endtask: b_transport

`endif // XACT__SV
