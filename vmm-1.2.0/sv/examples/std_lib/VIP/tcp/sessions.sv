//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

class tcp_client_session extends vmm_data;
   static vmm_log log = new("tcp_client_session", "class");

   rand bit [31:0] src_ip;
   rand bit [15:0] src_port;
   rand bit [15:0] dst_port;
   rand bit [31:0] dst_ip;

   typedef enum {CLOSED, SYN_SENT, ESTAB, FIN_WAIT} state_e;
   state_e state;

   rand bit [31:0] seqnum;
   rand bit [31:0] acknum;

   constraint tcp_client_session_valid {
      src_ip != dst_ip || src_port != dst_port;
      acknum == seqnum - 1;
   }

   function new();
      super.new(this.log);

      this.state = CLOSED;
   endfunction: new

   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%0sTCP Sessions #%0d.%0d.%0d", prefix,
               this.stream_id, this.scenario_id, this.data_id);
      $sformat(psdisplay, "%0s\n%0s   %0d.%0d.%0d.%0d/%0d->%0d.%0d.%0d.%0d/%0d",
               psdisplay, prefix,
               this.src_ip[31:24], this.src_ip[23:16], this.src_ip[15:8], this.src_ip[7:0], this.src_port,
               this.dst_ip[31:24], this.dst_ip[23:16], this.dst_ip[15:8], this.dst_ip[7:0], this.dst_port);
      $sformat(psdisplay, "%0s\n%0s   State=%0d, Next Seq: %h, Ack'd: %h",
               psdisplay, prefix, state, this.seqnum, this.acknum);
   endfunction: psdisplay

   virtual function vmm_data allocate();
      tcp_client_session cl = new;
      allocate = cl;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      tcp_client_session cl;

      if (to == null) cl = new;
      else if (!$cast(cl, to)) `vmm_fatal(this.log, "Cannot copy to non-tcp_client_session instance");

      void'(super.copy_data(cl));

      cl.src_ip   = this.src_ip;
      cl.src_port = this.src_port;
      cl.dst_ip   = this.dst_ip;
      cl.dst_port = this.dst_port;
      cl.state    = this.state;
      cl.seqnum   = this.seqnum;
      cl.acknum   = this.acknum;

      copy = cl;
   endfunction: copy
   
endclass: tcp_client_session


class tcp_client_packet extends tcp_packet;

   tcp_client_session client;


   function new(tcp_client_session client);
      super.new();
      this.client = client;
   endfunction: new

   virtual function vmm_data allocate();
      tcp_client_packet pk = new(null);
      allocate = pk;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      tcp_client_packet pk;

      if (to == null) pk = new(this.client);
      else if (!$cast(pk, to)) `vmm_fatal(this.log, "Cannot copy to non-tcp_client_packet instance");

      void'(super.copy(pk));
      pk.client = this.client;

      copy = pk;
   endfunction: copy
   
endclass: tcp_client_packet



// Example 5-39
class tcp_client_selector;
   int max_n_clients;
   int n_clients;

   rand bit new_client;
   rand int unsigned client_id;

   constraint tcp_client_selector_valid {
      if (n_clients > 0) client_id < n_clients;
   }

   constraint boundaries {
      if (n_clients >= max_n_clients) new_client == 0;
      if (n_clients == 0)             new_client == 1;
   }
   
endclass: tcp_client_selector


// Example 5-40
// Example 5-41
class tcp_client_action;
   tcp_client_session client;

   typedef enum {OPEN, CHAT, CLOSE} action_e;
   rand action_e action;

   rand tcp_packet pkt;

   constraint open_iff_before_established {
      if (client.state < tcp_client_session::ESTAB) action == OPEN;
      else                                           action != OPEN;
   }

   constraint close_if_past_established {
      if (client.state > tcp_client_session::ESTAB) action == CLOSE;
   }

   constraint valid_addresses {
      pkt.dst_ip   == client.dst_ip;
      pkt.dst_port == client.dst_port;
      pkt.src_ip   == client.src_ip;
      pkt.src_port == client.src_port;
   }

   constraint valid_seqnum {
      pkt.seqnum == client.seqnum;
   }

   constraint never_ack {
      pkt.ack == 0;
   }

   constraint never_rst {
      pkt.rst == 0;
   }

   // Example 5-41
   constraint syn_iff_open {
      if (action == OPEN) pkt.syn == 1;
      else                pkt.syn == 0;
   }

   constraint no_syn_nor_fin_if_chat {
      if (action == CHAT) {
         pkt.syn == 0;
         pkt.fin == 0;
      }
   }

   constraint fin_iff_close {
      if (action == CLOSE) pkt.fin == 1;
      else                 pkt.fin == 0;
   }

   function new();
      this.pkt = new;
   endfunction: new
endclass: tcp_client_action


class tcp_sessions_cfg;
   rand int unsigned max_n_clients;
   rand int unsigned hold_for_n_actions;

   constraint reasonable {
      max_n_clients      == 5;
      hold_for_n_actions == 10;
   }

   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%s%0d max clients, hold for %0d actions",
               prefix, this.max_n_clients, this.hold_for_n_actions);
   endfunction: psdisplay
endclass: tcp_sessions_cfg


class tcp_sessions extends vmm_xactor;
   tcp_sessions_cfg cfg;

   tcp_client_session  randomized_client;
   tcp_client_selector select;
   tcp_client_action   randomized_action;

   tcp_packet_channel in_chan;
   tcp_packet_channel out_chan;

   tcp_client_session clients[$];

   int DONE;

   typedef enum {RAMP_UP, HOLD, RAMP_DOWN} state_e;
   state_e state;

   function new(string             inst,
                int                stream_id      = -1,
                tcp_sessions_cfg   cfg,
                tcp_packet_channel in_chan        = null,
                tcp_packet_channel out_chan       = null,
                tcp_client_session client_factory = null,
                tcp_client_action  action_factory = null);
      super.new("TCP Session Generator", inst, stream_id);

      this.cfg = cfg;

      if (in_chan == null) in_chan = new("TCP Session Generator Input Channel", inst);
      this.in_chan = in_chan;

      if (out_chan == null) out_chan = new("TCP Session Generator Output Channel", inst);
      this.out_chan = out_chan;

      this.log.is_above(this.in_chan.log);
      this.log.is_above(this.out_chan.log);

      if (client_factory == null) client_factory = new;
      this.randomized_client = client_factory;

      if (action_factory == null) action_factory = new;
      this.randomized_action = action_factory;

      this.select = new;

      this.DONE = this.notify.configure();
   endfunction: new

   virtual task main();
      tcp_client_session client;

      int n_actions = 0;
      bit ok;

      fork
         super.main();
      join_none

      this.state = RAMP_UP;

      while (this.state != RAMP_DOWN || this.clients.size() > 0) begin

         case (state)
         RAMP_UP: if (this.clients.size() >= this.cfg.max_n_clients) begin
            `vmm_trace(this.log, "Holding number of sessions...");
            state = HOLD;
            n_actions = 0;
         end
         HOLD   : if (n_actions >= this.cfg.hold_for_n_actions) begin
            `vmm_trace(this.log, "Ramping down number of sessions...");
            state = RAMP_DOWN;
         end
         endcase

         n_actions++;

         this.select.max_n_clients = this.cfg.max_n_clients;
         this.select.n_clients     = this.clients.size();

         ok = this.select.randomize() with {
            if (this.state == RAMP_UP) new_client dist {1:/10, 0:/1};
            else                       new_client dist {1:/1,  0:/10};
         };
         if (!ok) `vmm_fatal(this.log, "Unable to randomize client selector");

         if (this.select.new_client) begin
            `vmm_trace(this.log, "Creating a new client...");
            ok = this.randomized_client.randomize();
            if (!ok) `vmm_fatal(this.log, "Unable to randomize new client descriptor");

            $cast(client, this.randomized_client.copy());
            this.clients.push_back(client);
         end else begin
            // Pick an existing client
            `vmm_debug(this.log, "Using existing client...");
            client = this.clients[this.select.client_id];
         end

         `vmm_debug(this.log, $psprintf("Using session:\n%s", client.psdisplay("   ")));

         // Move the client session forward
         this.randomized_action.client = client;
         ok = this.randomized_action.randomize();
         if (!ok) `vmm_fatal(this.log, "Unable to randomize next packet for client");

         // Send packet to TCP server
         begin
            tcp_packet pkt;

            $cast(pkt, this.randomized_action.pkt.copy());
            `vmm_debug(this.log, $psprintf("Sending TCP packet:\n%s",
                                           pkt.psdisplay("   ")));
            this.out_chan.put(pkt);

            // Move the state of the connection
            if (pkt.rst) client.state = tcp_client_session::CLOSED;
            else begin
               case (client.state)
                 tcp_client_session::CLOSED: begin
                    if (pkt.syn) client.state = tcp_client_session::SYN_SENT;
                 end
                 tcp_client_session::ESTAB: begin
                    if (pkt.fin) client.state = tcp_client_session::FIN_WAIT;
                 end
               endcase
            end
         end

         // Wait for the server response
         // (Should really be happening concurrently)
         if (client.state != tcp_client_session::CLOSED) begin
            tcp_packet pkt;

            this.in_chan.get(pkt);
            `vmm_debug(this.log, $psprintf("Received TCP packet:\n%s",
                                           pkt.psdisplay("   ")));

            // The response must be for the last client
            // (Should really look for the client targetted by the response)
            if (pkt.dst_ip != client.src_ip || pkt.dst_port != client.src_port ||
                pkt.src_ip != client.dst_ip || pkt.src_port != client.dst_port) begin
               `vmm_error(this.log, $psprintf("Received packet for unknown session:\n%s",
                                              pkt.psdisplay("   ")));
               continue;
            end

            // Example 5-43
            // Move the state of the connection
            if (pkt.rst) begin
               `vmm_warning(this.log, "Session was reset by server!");
               client.state = tcp_client_session::CLOSED;
            end
            else begin
               case (client.state)
                 tcp_client_session::SYN_SENT: begin
                    if (pkt.syn && pkt.ack) client.state = tcp_client_session::ESTAB;
                    else client.state = tcp_client_session::CLOSED;
                 end
                 tcp_client_session::FIN_WAIT: begin
                    if (pkt.fin && pkt.ack) client.state = tcp_client_session::CLOSED;
                 end
               endcase
            end
         end

         // Removed closed sessions
         if (client.state == tcp_client_session::CLOSED) begin
            foreach (this.clients[i]) begin
               if (this.clients[i] == client) begin
                  this.clients.delete(i);
                  `vmm_trace(this.log, $psprintf("Removed closed session:\n%s",
                                                 client.psdisplay("   ")));
                  client = null;
                  break;
               end
            end
            if (client != null) begin
               `vmm_fatal(this.log, "Client descriptor was not in client list");
            end
         end
      end

      this.notify.indicate(this.DONE);
      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      this.notify.reset(vmm_xactor::XACTOR_BUSY);
   endtask

endclass: tcp_sessions
