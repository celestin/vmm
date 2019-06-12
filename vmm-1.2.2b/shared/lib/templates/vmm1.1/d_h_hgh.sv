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
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: XACT_cfg


class XACT extends vmm_xactor;

   int EXECUTING;
   int SUB_EXECUTING;
   
   protected XACT_cfg cfg;
   local XACT_cfg reset_cfg;

   TR_channel in_chan;
   TX_channel exec_chan;

   extern function new(string inst = "",
                       int stream_id = -1,
                       XACT_cfg cfg = null,
                       TR_channel in_chan = null,
                       TX_channel exec_chan = null);

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
   extern protected virtual task main();
   extern protected virtual task tx_driver();

endclass: XACT


function XACT::new(string inst = "",
                   int stream_id = -1,
                   XACT_cfg cfg = null,
                   TR_channel in_chan = null,
                   TX_channel exec_chan = null);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING     = this.notify.configure(-1, vmm_notify::ON_OFF);
   this.SUB_EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);
   if (exec_chan == null) exec_chan = new("XACT Execution Channel", inst);
   this.exec_chan = exec_chan;

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
task XACT::main();
   super.main();

   fork
      tx_driver();
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

`endif // XACT__SV
