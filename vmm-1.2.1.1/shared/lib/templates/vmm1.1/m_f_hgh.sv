//
// Template for VMM-compliant full-duplex functional-level monitor
// <MON>       Name of monitor transactor
// <TR>         Name of high-level transaction descriptor class
// <TX>         Name of low-level transaction descriptor class
//

`ifndef MON__SV
`define MON__SV

`include "TR.sv"
`include "TX.sv"

typedef class MON;

class MON_callbacks extends vmm_xactor_callbacks;

   // ToDo: Add additional relevant callbacks
   // ToDo: Use a task if callbacks can be blocking

   // Called at end of observed lower-level transaction
   virtual function void post_tx_trans_obs(MON xactor,
                                           TX tx,
                                           bit drop);
   
   endfunction: post_tx_trans_obs


   virtual function void post_rx_trans_obs(MON xactor,
                                           TX tx,
                                           bit drop);
   
   endfunction: post_rx_trans_obs


   // Call when a high-level transaction has been identified
   virtual function void post_tx_trans(MON xactor,
                                       TX tx[$],
                                       TR tr,
                                       bit drop);
   
   endfunction: post_tx_trans


   virtual function void post_rx_trans(MON xactor,
                                       TX tx[$],
                                       TR tr,
                                       bit drop);
   
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

   //Performace recording for Tx channel of monitor 
   virtual task post_tx_trans_obs(XACT xactor,TX tr,bit drop);
      fork begin
         vmm_perf_tenure monitor_tx_tenure = new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(monitor_tx_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(monitor_tx_tenure);
      end join_none
   endtask: post_tx_trans_obs
   
   //Performace recording for Rx channel of monitor 
   virtual task post_rx_trans_obs(XACT xactor,TR tr, bit drop);
      fork begin
         vmm_perf_tenure monitor_rx_tenure= new(xactor.stream_id,,tr);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(monitor_rx_tenure);
          
         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         tr.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(monitor_rx_tenure);
      end join_none
   endtask: post_rx_trans_obs


endclass: MON_perf_cb
PERF_END


class MON_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: MON_cfg


class MON extends vmm_xactor;

   int OBS_T;
   int SUB_OBS_T;
   int OBS_R;
   int SUB_OBS_R;
   
   protected MON_cfg cfg;
   local MON_cfg reset_cfg;
   protected TR tx_factory;
   local TR reset_tx_factory;
   protected TR rx_factory;
   local TR reset_rx_factory;

   TR_channel tx_chan;
   TR_channel rx_chan;
   TX_channel tx_obs_chan;
   TX_channel rx_obs_chan;

   extern function new (string inst = "",
                        int stream_id = -1,
                        MON_cfg cfg = null,
                        TR_channel tx_chan = null,
                        TR_channel rx_chan = null,
                        TX_channel tx_obs_chan = null,
                        TX_channel rx_obs_chan = null,
                        TR tx_factory = null,
                        TR rx_factory = null);
   
   MACRO_START
   `vmm_xactor_member_begin(MON)
     `vmm_xactor_member_scalar(OBS_T, DO_ALL)
     `vmm_xactor_member_scalar(SUB_OBS_T, DO_ALL)
     `vmm_xactor_member_scalar(OBS_R, DO_ALL)
     `vmm_xactor_member_scalar(SUB_OBS_R, DO_ALL)
     `vmm_xactor_member_channel(tx_chan, DO_ALL)
     `vmm_xactor_member_channel(rx_chan, DO_ALL)
     `vmm_xactor_member_channel(tx_obs_chan, DO_ALL)
     `vmm_xactor_member_channel(rx_obs_chan, DO_ALL)
     //ToDo:  Add vmm xactor member

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
                  MON_cfg cfg = null,
                  TR_channel tx_chan = null,
                  TR_channel rx_chan = null,
                  TX_channel tx_obs_chan = null,
                  TX_channel rx_obs_chan = null,
                  TR tx_factory = null,
                  TR rx_factory = null);

   super.new("MON Transactor", inst, stream_id);

   this.OBS_T = this.notify.configure();
   this.SUB_OBS_T = this.notify.configure();
   this.OBS_R = this.notify.configure();
   this.SUB_OBS_R = this.notify.configure();

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (tx_chan == null) tx_chan = new("MON Tx Output Channel", inst);
   this.tx_chan = tx_chan;
   if (rx_chan == null) rx_chan = new("MON Rx Output Channel", inst);
   this.rx_chan = rx_chan;
   if (tx_obs_chan == null) tx_obs_chan = new("MON Tx Observation Channel", inst);
   this.tx_obs_chan = tx_obs_chan;
   if (rx_obs_chan == null) rx_obs_chan = new("MON Rx Observation Channel", inst);
   this.rx_obs_chan = rx_obs_chan;

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
   this.tx_obs_chan.flush();
   this.rx_obs_chan.flush();

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
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.tx_obs_chan);
      this.tx_obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(MON_callbacks,
                    post_tx_trans_obs(this, tx[tx.size()-1], drop));
       tx[tx.size()-1].notify.indicate(vmm_data::STARTED);
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBS_T, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level Tx transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction

      $cast(tr, this.tx_factory.copy());
      
      if (tr != null) begin
          drop = 0;
         
         `vmm_callback(MON_callbacks,
                       post_tx_trans(this, tx, tr, drop));

         if (!drop) begin
            this.notify.indicate(this.OBS_T, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.tx_chan.sneak(tr);
         end
         tx[tx.size()-1].notify.indicate(vmm_data::ENDED);
         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end

endtask: tx_monitor


task MON::rx_monitor();

   forever begin
      TR tr;
      TX tx[$];
      TX tmp_tx;
      bit drop;

      tr = null;
      
      this.wait_if_stopped_or_empty(this.rx_obs_chan);
      this.rx_obs_chan.get(tmp_tx);
      tx.push_back(tmp_tx);

      drop = 0;
      `vmm_callback(MON_callbacks,
                    post_rx_trans_obs(this, tx[tx.size()-1], drop));
      tx[tx.size()-1].notify.indicate(vmm_data::STARTED);
      if (drop) begin
         tx.pop_back();
         continue;
      end
   
      this.notify.indicate(this.SUB_OBS_R, tx[tx.size()-1]);

      `vmm_debug(this.log, "Observed lower-level Rx transaction...");
      `vmm_verbose(this.log, tx[tx.size()-1].psdisplay("   "));

      // ToDo: Check if the lower-level transactions observed so far
      //       create a higher-level transaction

      $cast(tr, this.rx_factory.copy());
      
      if (tr != null) begin
         drop = 0;
         
         `vmm_callback(MON_callbacks,
                       post_rx_trans(this, tx, tr, drop));
         SCB_INT_MTHD_TWO_START
         this.exp_vmm_sb_ds(tr);
         SCB_INT_MTHD_TWO_END
 
         if (!drop) begin
            this.notify.indicate(this.OBS_R, tr);

            `vmm_trace(this.log, "Observed transaction...");
            `vmm_debug(this.log, tr.psdisplay("   "));
         
            this.rx_chan.sneak(tr);
         end
         tx[tx.size()-1].notify.indicate(vmm_data::ENDED);
         // ToDo: removed the interpreted observed sub transactions
         tx.delete();
      end
   end

endtask: rx_monitor

`endif
