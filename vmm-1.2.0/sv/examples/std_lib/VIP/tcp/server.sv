//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

typedef class tcp_server_packet;

class tcp_server_session;
   static vmm_log log = new("tcp_server_session", "class");

   bit [31:0] src_ip;
   bit [15:0] src_port;
   bit [15:0] dst_port;
   bit [31:0] dst_ip;

   typedef enum {LISTEN, ESTAB, CLOSE_WAIT, RESET, CLOSED} state_e;
   state_e state;

   bit [31:0] acknum;

   tcp_packet last_pkt;
   tcp_packet randomized_pkt;

   function new(bit [31:0] src_ip,
                bit [15:0] src_port,
                bit [31:0] dst_ip,
                bit [15:0] dst_port,
                bit [31:0] acknum,
                tcp_packet pkt_factory = null);
      this.dst_ip   = src_ip;
      this.dst_port = src_port;
      this.src_ip   = dst_ip;
      this.src_port = dst_port;
      this.acknum   = acknum;

      this.state = LISTEN;

      if (pkt_factory == null) begin
         tcp_server_packet pkt = new(this);
         this.randomized_pkt = pkt;
      end
      else this.randomized_pkt = pkt_factory;
   endfunction: new


   function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%0sTCP Session:", prefix);
      $sformat(psdisplay, "%0s\n%0s   %0d.%0d.%0d.%0d/%0d->%0d.%0d.%0d.%0d/%0d",
               psdisplay, prefix,
               this.src_ip[31:24], this.src_ip[23:16], this.src_ip[15:8], this.src_ip[7:0], this.src_port,
               this.dst_ip[31:24], this.dst_ip[23:16], this.dst_ip[15:8], this.dst_ip[7:0], this.dst_port);
      $sformat(psdisplay, "%0s\n%0s   State=%0d, Ack'd: %h",
               psdisplay, prefix, state, this.acknum);
   endfunction: psdisplay

endclass: tcp_server_session


class tcp_server_packet extends tcp_packet;

   tcp_server_session session;

   constraint valid_addresses {
      dst_ip   == session.dst_ip;
      dst_port == session.dst_port;
      src_ip   == session.src_ip;
      src_port == session.src_port;
   }

   constraint valid_acknum {
      acknum == session.acknum;
   }

   constraint rst_iff_reset {
      if (session.state == tcp_server_session::RESET) rst == 1;
      else                                            rst == 0;
   }

   constraint always_ack {
      ack == 1;
   }

   constraint syn_ack_iff_listen {
      if (session.state == tcp_server_session::LISTEN) syn == 1;
      else                                             syn == 0;
   }

   constraint fin_ack_iff_close_wait {
      if (session.state == tcp_server_session::CLOSE_WAIT) fin == 1;
      else                                                 fin == 0;
   }

   function new(tcp_server_session session);
      super.new();
      this.session = session;
   endfunction: new

   virtual function vmm_data allocate();
      tcp_server_packet pk = new(null);
      allocate = pk;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      tcp_server_packet pk;

      if (to == null) pk = new(this.session);
      else if (!$cast(pk, to)) `vmm_fatal(this.log, "Cannot copy to non-tcp_server_packet instance");

      void'(super.copy(pk));
      pk.session = this.session;

      copy = pk;
   endfunction: copy
   
endclass: tcp_server_packet


class tcp_server extends vmm_xactor;
   tcp_packet         pkt_factory;

   tcp_packet_channel in_chan;
   tcp_packet_channel out_chan;

   tcp_server_session clients[$];

   function new(string             inst,
                int                stream_id       = -1,
                tcp_packet_channel in_chan         = null,
                tcp_packet_channel out_chan        = null,
                tcp_packet         pkt_factory     = null);
      super.new("TCP Server", inst, stream_id);

      if (in_chan == null) in_chan = new("TCP Server Input Channel", inst);
      this.in_chan = in_chan;

      if (out_chan == null) out_chan = new("TCP Server Output Channel", inst);
      this.out_chan = out_chan;

      this.log.is_above(this.in_chan.log);
      this.log.is_above(this.out_chan.log);

      this.pkt_factory = pkt_factory;
   endfunction: new

   virtual task main();
      tcp_server_session client;

      bit ok;

      fork
         super.main();
      join_none

      forever begin
         tcp_packet         pkt;
         tcp_server_session client;
         int                client_id;

         // Wait for client requests
         this.wait_if_stopped_or_empty(this.in_chan);
         this.in_chan.get(pkt);

         // Check if this is an existing session...
         foreach (this.clients[i]) begin
            if (pkt.dst_ip != this.clients[i].src_ip || pkt.dst_port != this.clients[i].src_port ||
                pkt.src_ip != this.clients[i].dst_ip || pkt.src_port != this.clients[i].dst_port) continue;
            client = this.clients[i];
            client_id = i;
         end
         if (client == null) begin
            client = new(pkt.src_ip, pkt.src_port, pkt.dst_ip, pkt.dst_port, pkt.seqnum-1,
                         this.pkt_factory);
            client_id = this.clients.size();
            this.clients.push_back(client);
         end

         `vmm_debug(this.log, $psprintf("Using session:\n%s", client.psdisplay("   ")));

         // Move the state of the connection
         if (pkt.rst) begin
            `vmm_warning(this.log, "Session was reset by client!");
            client.state = tcp_server_session::CLOSED;
         end
         else begin
            case (client.state)
              tcp_server_session::ESTAB: begin
                 if (pkt.fin) client.state = tcp_server_session::CLOSE_WAIT;
                 if (pkt.syn) begin
                    `vmm_error(this.log, "SYN packet received in ESTABLISHED session");
                    client.state = tcp_server_session::RESET;
                 end
              end
            endcase

            // Move the client session forward
            client.last_pkt = pkt;
            ok = client.randomized_pkt.randomize();
            if (!ok) `vmm_fatal(this.log, "Unable to randomize next packet for client");

            // Send packet to TCP client
            begin
               tcp_packet pkt;

               $cast(pkt, client.randomized_pkt.copy());
               `vmm_debug(this.log, $psprintf("Sending TCP packet:\n%s",
                                              pkt.psdisplay("   ")));
               this.out_chan.put(pkt);

               // Move the state of the connection
               case (client.state)
                 tcp_server_session::LISTEN: begin
                    if (pkt.ack) client.state = tcp_server_session::ESTAB;
                 end
               endcase
            end
         end

         // Removed closed sessions
         if (client.state == tcp_server_session::CLOSED) begin
            if (client != this.clients[client_id]) begin
               `vmm_fatal(this.log, "Client descriptor and id out of sync");
            end
            this.clients.delete(client_id);
            `vmm_trace(this.log, $psprintf("Removed closed session:\n%s",
                                           client.psdisplay("   ")));
            client = null;
         end
      end
   endtask

endclass: tcp_server
