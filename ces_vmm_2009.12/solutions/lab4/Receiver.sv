//
// Template for VMM-compliant half-duplex physical-level monitor
//

`ifndef RECEIVER__SV
`define RECEIVER__SV

`include "router_io.sv"
`include "Packet.sv"

typedef class Receiver;

class Receiver_callbacks extends vmm_xactor_callbacks;

  // ToDo: Add additional relevant callbacks
  // ToDo: Use a task if callbacks can be blocking

   // Called at start of observed transaction
   virtual function void pre_trans(Receiver xactor,
                                   Packet tr);
   
   endfunction: pre_trans


   // Called before acknowledging a transaction
   virtual function pre_ack(Receiver xactor,
                            Packet tr);
   
   endfunction: pre_ack
   

   // Called at end of observed transaction
   virtual function void post_trans(Receiver xactor,
                                    Packet tr);
   
   endfunction: post_trans
   
   // Callback method post_cb_trans can be used for coverage
   virtual task post_cb_trans(Receiver xactor,
                              Packet tr);
   
   endtask: post_cb_trans

endclass: Receiver_callbacks


class Receiver_cfg;
   // ToDo: Add transactor configuration class properties
   rand int mode;

endclass: Receiver_cfg


class Receiver extends vmm_xactor;

   int OBSERVING;
   
   protected Receiver_cfg cfg;
   local Receiver_cfg reset_cfg;
   protected Packet rx_factory;
   local Packet reset_rx_factory;

   Packet_channel out_chan;
   virtual router_io.slave sigs;

   extern function new(string inst = "",
                       int stream_id = -1,
                       virtual router_io.slave sigs,
                       Receiver_cfg cfg = null,
                       Packet_channel out_chan = null,
                       Packet rx_factory = null);

   extern virtual function void reconfigure(Receiver_cfg cfg);
   extern virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
   extern protected virtual task main();
   extern virtual task recv(Packet tr);
endclass: Receiver
`include "recv.sv"


function Receiver::new(string inst = "",
                  int stream_id = -1,
                  virtual router_io.slave  sigs,
                  Receiver_cfg cfg = null,
                  Packet_channel out_chan = null,
                  Packet rx_factory = null);

   super.new("Receiver Transactor", inst, stream_id);

   this.OBSERVING = this.notify.configure(-1, vmm_notify::ON_OFF);

   this.sigs = sigs;

   if (cfg == null) cfg = new;
   this.cfg = cfg;
   this.reset_cfg = cfg;

   if (out_chan == null) out_chan = new("Receiver Output Channel", inst);
   this.out_chan = out_chan;

   if (rx_factory == null) rx_factory = new;
   this.rx_factory = rx_factory;
   this.reset_rx_factory = rx_factory;

endfunction: new


function void Receiver::reconfigure(Receiver_cfg cfg);

   if (!this.notify.is_on(XACTOR_IDLE)) begin
      `vmm_warning(this.log, "Transactor should be reconfigured only when IDLE");
   end

   this.cfg = cfg;
   
   // ToDo: Notify any running threads of the new configuration
endfunction: reconfigure


function void Receiver::reset_xactor(reset_e rst_typ = SOFT_RST);

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


task Receiver::main();
   super.main();

   forever begin
      Packet tr;

      // ToDo: Wait for start of transaction

      $cast(tr, this.rx_factory.copy());
      `vmm_callback(Receiver_callbacks, pre_trans(this, tr));

      this.recv(tr);

      `vmm_callback(Receiver_callbacks, post_trans(this, tr));

      this.out_chan.sneak(tr);
   end

endtask: main

`endif // RECEIVER__SV
