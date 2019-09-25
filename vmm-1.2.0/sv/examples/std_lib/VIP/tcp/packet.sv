//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

//
// *INCOMPLETE TCP packet definition*
//


class tcp_opts;
   typedef enum {END_OF_OPTS, NOP, MAX_SEG_SIZE} options_e;
   rand options_e option;
   
   rand bit [15:0] max_seg_size; // If MAX_SEG_SIZE
endclass: tcp_opts
  

class tcp_packet extends vmm_data;

   static vmm_log log = new("tcp_packet", "class");

   rand bit [31:0] src_ip;
   rand bit [15:0] src_port;
   rand bit [15:0] dst_port;
   rand bit [31:0] dst_ip;
   rand bit [31:0] seqnum;
   rand bit [31:0] acknum;
   rand bit [ 3:0] data_offset;
   rand bit [ 5:0] reserved;
   rand bit        urg;
   rand bit        ack;
   rand bit        psh;
   rand bit        rst;
   rand bit        syn;
   rand bit        fin;
   rand bit [15:0] window;
   rand bit [15:0] checksum;
   rand bit [15:0] urg_ptr;
   rand tcp_opts   options[];
   rand bit [31:0] data[];


   function new();
      super.new(this.log);
   endfunction: new

   extern virtual function string psdisplay(string prefix = "");

   virtual function vmm_data allocate();
      tcp_packet pk = new;
      allocate = pk;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      tcp_packet pk;

      if (to == null) pk = new;
      else if (!$cast(pk, to)) `vmm_fatal(this.log, "Cannot copy to non-tcp_packet instance");

      super.copy_data(pk);

      pk.src_ip   = this.src_ip;
      pk.src_port = this.src_port;
      pk.dst_ip   = this.dst_ip;
      pk.dst_port = this.dst_port;
      pk.seqnum   = this.seqnum;
      pk.acknum   = this.acknum;
      pk.data_offset = this.data_offset;
      pk.reserved    = this.reserved;
      pk.urg         = this.urg;
      pk.ack         = this.ack;
      pk.psh         = this.psh;
      pk.rst         = this.rst;
      pk.syn         = this.syn;
      pk.fin         = this.fin;
      pk.window      = this.window;
      pk.checksum    = this.checksum;
      pk.urg_ptr     = this.urg_ptr;
      //pk.options     = this.options;
      pk.data        = new [this.data.size()] (this.data);      

      copy = pk;
   endfunction: copy
   
endclass: tcp_packet

`vmm_channel(tcp_packet)


function string tcp_packet::psdisplay(string prefix);
   $sformat(psdisplay, "%0sTCP Packet #%0d.%0d.%0d", prefix,
            this.stream_id, this.scenario_id, this.data_id);
   $sformat(psdisplay, "%0s\n%0s   %0d.%0d.%0d.%0d/%0d->%0d.%0d.%0d.%0d/%0d: %0s/%0s/%0s/%0s",
            psdisplay, prefix,
            this.src_ip[31:24], this.src_ip[23:16], this.src_ip[15:8], this.src_ip[7:0], this.src_port,
            this.dst_ip[31:24], this.dst_ip[23:16], this.dst_ip[15:8], this.dst_ip[7:0], this.dst_port,
            (this.rst) ? "Rst" : "",
            (this.syn) ? "Syn" : "",
            (this.fin) ? "Fin" : "",
            (this.ack) ? "Ack" : "");
endfunction: psdisplay
