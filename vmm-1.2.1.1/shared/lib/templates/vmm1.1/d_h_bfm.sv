//
// Template for VMM-compliant half-duplex physical-level transactor
// <XACT>       Name of transactor
// <IF>         Name of physical interface
// <TR>         Name of input transaction descriptor class
//

`ifndef XACT__SV
`define XACT__SV

`include "IF.sv"
`include "TR.sv"

typedef class XACT;

class XACT_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use "task" if callbacks cannot be blocking

   // Called before a transaction is executed
   virtual function void pre_trans(XACT xactor,
                                   TR tr,
                                   ref bit drop);
     // ToDo: Add relevant code
   endfunction: pre_trans

   // Called after a transaction has been executed
   virtual function void post_trans(XACT xactor,
                                    TR tr);
     // ToDo: Add relevant code
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

   protected XACT_cfg cfg;
   local XACT_cfg reset_cfg;

   TR_channel in_chan;
   virtual IF.master sigs;

   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual IF.master sigs,
                       XACT_cfg cfg = null,
                       TR_channel in_chan = null);
 
MACRO_START
   `vmm_xactor_member_begin(XACT)
      `vmm_xactor_member_scalar(EXECUTING, DO_ALL)
      `vmm_xactor_member_channel(in_chan, DO_ALL)
      // ToDo: Add vmm xactor member

   `vmm_xactor_member_end(XACT)

   // ToDo: Add required short hand override method
MACRO_END
   extern virtual function void reconfigure(XACT_cfg cfg);
   NORMAL_START
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   NORMAL_END
   extern protected virtual task main();
   extern protected virtual task send(TR tr);

endclass: XACT


function XACT::new(string inst = "",
                   int stream_id = -1,
                   virtual IF.master sigs,
                   XACT_cfg cfg = null,
                   TR_channel in_chan = null);

   super.new("XACT Transactor", inst, stream_id);

   this.EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("XACT Input Channel", inst);
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);

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

   // ToDo: Reset output signals

   this.sigs.mck1.sync_txd <= 0;
   this.sigs.mck1.sync_dat <= 'z;
   this.sigs.async_en      <= 0;

   this.in_chan.flush();

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

   forever begin
      TR tr;
      bit drop;

      // ToDo: Set output signals to their idle state
      this.sigs.mck1.sync_txd <= 0;
      this.sigs.mck1.sync_dat <= 'z;
      this.sigs.async_en      <= 0;
      
      this.wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);

      drop = 0;
      `vmm_callback(XACT_callbacks,pre_trans(this, tr, drop));
      if (drop) begin
         void'(this.in_chan.remove());
         continue;
      end
      void'(this.in_chan.start());
      this.notify.indicate(this.EXECUTING, tr);

      `vmm_trace(this.log, "Starting transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      case (tr.kind) 
         TR::READ: begin
            // ToDo: Implement READ transaction
         end

         TR::WRITE: begin
            // ToDo: Implement READ transaction
         end
      endcase

      this.notify.reset(this.EXECUTING);

      send(tr);  

      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      `vmm_callback(XACT_callbacks,post_trans(this, tr));
    
      void'(this.in_chan.remove());
   end
endtask: main

task XACT::send(TR tr);
   // ToDo: Drive signal on interface
  
endtask: send

`endif // XACT__SV
