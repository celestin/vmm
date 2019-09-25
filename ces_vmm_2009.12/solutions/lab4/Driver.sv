//
// Template for VMM-compliant half-duplex physical-level transactor
//

`ifndef DRIVER__SV
`define DRIVER__SV

`include "router_io.sv"
`include "Packet.sv"

typedef class Driver;

class Driver_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use "task" if callbacks cannot be blocking

   // Called before a transaction is executed
   virtual function void pre_trans(Driver xactor,
                                   Packet tr,
                                   ref bit drop);
     // ToDo: Add relevant code
   endfunction: pre_trans

   // Called after a transaction has been executed
   virtual function void post_trans(Driver xactor,
                                    Packet tr);
     // ToDo: Add relevant code
   endfunction: post_trans

endclass: Driver_callbacks


class Driver_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: Driver_cfg


class Driver extends vmm_xactor;

   int EXECUTING;

   protected Driver_cfg cfg;
   local Driver_cfg reset_cfg;

   Packet_channel in_chan;
   virtual router_io.master sigs;

   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual router_io.master sigs,
                       Driver_cfg cfg = null,
                       Packet_channel in_chan = null);
 
   extern virtual function void reconfigure(Driver_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();
   extern protected virtual task send(Packet tr);
   extern virtual task send_address(Packet tr);
   extern virtual task send_pad(Packet tr);
   extern virtual task send_payload(Packet tr);
endclass: Driver
`include "send.sv"


function Driver::new(string inst = "",
                   int stream_id = -1,
                   virtual router_io.master sigs,
                   Driver_cfg cfg = null,
                   Packet_channel in_chan = null);

   super.new("Driver Transactor", inst, stream_id);

   this.EXECUTING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (in_chan == null) in_chan = new("Driver Input Channel", inst);
   this.in_chan = in_chan;
   this.in_chan.set_consumer(this);

endfunction: new


function void Driver::reconfigure(Driver_cfg cfg);

   if (!this.notify.is_on(XACTOR_IDLE)) begin
      `vmm_warning(this.log, "Transactor should be reconfigured only when IDLE");
   end

   this.cfg = cfg;
   
   // ToDo: Notify any running threads of the new configuration
endfunction: reconfigure


function void Driver::reset_xactor(reset_e rst_typ = SOFT_RST);

   super.reset_xactor(rst_typ);

   // ToDo: Reset output signals

   this.sigs.mclk.frame_n[stream_id] <= 1'b1;
   this.sigs.mclk.valid_n[stream_id] <= 1'b1;

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


task Driver::main();
   super.main();

   forever begin
      Packet tr;
      bit drop;

      // ToDo: Set output signals to their idle state
      this.sigs.mclk.frame_n[stream_id] <= 1'b1;
      this.sigs.mclk.valid_n[stream_id] <= 1'b1;
      
      this.wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);

      drop = 0;
      `vmm_callback(Driver_callbacks,pre_trans(this, tr, drop));
      if (drop) begin
         void'(this.in_chan.remove());
         continue;
      end
      void'(this.in_chan.start());
      this.notify.indicate(this.EXECUTING, tr);

      `vmm_trace(this.log, "Starting transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      this.send(tr);

      this.notify.reset(this.EXECUTING);

      void'(this.in_chan.complete());

      `vmm_trace(this.log, "Completed transaction...");
      `vmm_debug(this.log, tr.psdisplay("   "));

      `vmm_callback(Driver_callbacks,post_trans(this, tr));
    
      void'(this.in_chan.remove());
   end
endtask: main

task Driver::send(Packet tr);
   if (tr.sa == this.stream_id) begin
      send_address(tr);
      send_pad(tr);
      send_payload(tr);
   end
endtask: send

`endif // DRIVER__SV
