//
// Template for VMM-compliant full-duplex functional-level transactor
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

  // ToDo: Add additional relevant callbacks
  // ToDo: Use task if callbacks can be blocking

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


   virtual function void post_trans_exec(XACT xactor,
                                         TR tr,
                                         TX tx[$]);
   endfunction: post_trans_exec


   // Called after a transaction has been executed
   virtual task post_in_trans(XACT xactor,
                              TR tr);
   endtask: post_in_trans


   // Called at end of observed lower-level transaction
   virtual function void post_trans_obs(XACT xactor,
                                        TX tx,
                                        bit drop);
   endfunction: post_trans_obs


   // Call when a high-level transaction has been identified
   virtual function void post_out_trans(XACT xactor,
                                        TX tx[$],
                                        TR tr,
                                        bit drop);
   endfunction: post_out_trans

endclass: XACT_callbacks

PERF_START
class XACT_perf_cb extends vmm_xactor_callbacks;

   vmm_perf_analyzer perf;
  
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction:new
   
  //Performace recording for Driving channel (Execute) of functional driver 
   virtual task pre_exec(XACT xactor,TX tr,ref bit drop);
      fork begin
         vmm_perf_tenure driver_ex_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(driver_ex_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(driver_ex_tenure);
      end join_none
   endtask: pre_exec 

  //ToDo: User can add the performance recording for observing channel of functional driver

 
endclass: XACT_perf_cb
PERF_END

class XACT_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: XACT_cfg


class XACT extends vmm_xactor;

  int EXECUTING;
  int SUB_EXECUTING;
  int OBSERVED;
  int SUB_OBSERVED;
  
  protected XACT_cfg cfg;
  local XACT_cfg reset_cfg;
  protected TR rx_factory;
  local TR reset_rx_factory;

  TR_channel in_chan;
  TR_channel out_chan;
  TX_channel exec_chan;
  TX_channel obs_chan;

  extern function new (string inst = "",
                       int stream_id = -1,
                       XACT_cfg cfg = null,
                       TR_channel in_chan = null,
                       TR_channel out_chan = null,
                       TX_channel exec_chan = null,
                       TX_channel obs_chan = null,
                       TR rx_factory = null);

  MACRO_START
  `vmm_xactor_member_begin(XACT)
    `vmm_xactor_member_scalar(EXECUTING, DO_ALL)
    `vmm_xactor_member_scalar(SUB_EXECUTING, DO_ALL)
    `vmm_xactor_member_scalar(OBSERVED, DO_ALL)
    `vmm_xactor_member_scalar(SUB_OBSERVED, DO_ALL)
    `vmm_xactor_member_channel(in_chan, DO_ALL)
    `vmm_xactor_member_channel(out_chan, DO_ALL)
    `vmm_xactor_member_channel(exec_chan, DO_ALL)
    `vmm_xactor_member_channel(obs_chan, DO_ALL)
    //ToDo: Add vmm xactor member

  `vmm_xactor_member_end(XACT)
  
  //ToDo: Add required short hand override method

  MACRO_END
  NORMAL_START
  extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
  NORMAL_END
  extern virtual function void reconfigure(XACT_cfg cfg);
  extern protected virtual task tx_driver();
  extern protected virtual task rx_monitor();
  extern protected virtual task main();

endclass: XACT


function XACT::new(string inst ="",
                   int stream_id = -1,
                   XACT_cfg cfg = null,
                   TR_channel in_chan = null,
                   TR_channel out_chan = null,
                   TX_channel exec_chan = null,
                   TX_channel obs_chan = null,
                   TR rx_factory = null);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING     = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.SUB_EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.OBSERVED      = this.notify.configure();
   this.SUB_OBSERVED  = this.notify.configure();

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);

   if (out_chan == null) out_chan = new("XACT Output Channel", inst);
   this.out_chan = out_chan;
   if (exec_chan == null) exec_chan = new("XACT Execution Channel", inst);
   this.exec_chan = exec_chan;
   if (obs_chan == null) obs_chan = new("XACT Observation Channel", inst);
   this.obs_chan = obs_chan;

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

   this.in_chan.flush();
   this.out_chan.flush();
   this.exec_chan.flush();
   this.obs_chan.flush();

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
      // ToDo: User need to add driving logic and remove "#0;"

      // ToDo: User need to add driving logic and remove $finish;"
     `vmm_note(log, "User need to add driving logic and remove $finish");
      $finish;

      `vmm_callback(XACT_callbacks,
                    pre_trans_exec(this, tr, tx));

      foreach (tx[i]) begin
         drop = 0;
         `vmm_callback(XACT_callbacks,
                       pre_exec(this, tx[i], drop));
         if (drop) continue;

         this.notify.indicate(this.SUB_EXECUTING, tx[i]);

         tx[i].notify.indicate(vmm_data::STARTED); 
         `vmm_debug(this.log, "Executing lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         
         this.exec_chan.put(tx[i]);

         // ToDo: Add completion model if not blocking
         
         this.notify.reset(this.SUB_EXECUTING);

         `vmm_debug(this.log, "Executed lower-level transaction...");
         `vmm_verbose(this.log, tx[i].psdisplay("   "));
         tx[i].notify.indicate(vmm_data::ENDED); 
         
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
                    post_in_trans(this, tr));

      void'(this.in_chan.remove());
   end
endtask: tx_driver


task XACT::rx_monitor();

   forever begin
      TR tr;
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.obs_chan);
      this.obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(XACT_callbacks,
                    post_trans_obs(this, tx[tx.size()-1], drop));
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBSERVED, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction
      // ToDo: User need to add monitoring logic and remove "#0;"

      // ToDo: User need to add monitoring logic and remove $finish;"
     `vmm_note(log, "User need to add monitoring logic and remove $finish");
      $finish;
      $cast(tr, this.rx_factory.copy());
      
      if (tr != null) begin
         drop = 0;
         
         `vmm_callback(XACT_callbacks,
                       post_out_trans(this, tx, tr, drop));

         if (!drop) begin
            this.notify.indicate(this.OBSERVED, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.out_chan.sneak(tr);
         end

         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end
endtask: rx_monitor

`endif // XACT__SV
