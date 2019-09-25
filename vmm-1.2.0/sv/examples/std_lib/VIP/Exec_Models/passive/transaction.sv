//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "vmm.sv"

`ifndef TR_HAS_BEEN_INCLUDED
`define TR_HAS_BEEN_INCLUDED

class transaction extends vmm_data;

   static vmm_log log = new("transaction", "class");

   typedef enum {READ, WRITE} kind_e;
   typedef enum {X , ACK, NAK, RETRY} status_e;

   rand kind_e kind;
   rand bit [1:0] addr;
   rand bit [7:0] data;

   status_e status;

   function new();
      super.new(log);

      status = X;
   endfunction: new

   virtual function string psdisplay(string prefix = "");
      psdisplay = $psprintf("%s(#%0d) %s @ 'h%h = 'h%2h (%s)",
                            prefix, this.data_id,
                            (kind == READ) ? "Read" : "Write",
                            addr, data, status_image(status));
   endfunction: psdisplay

   virtual function string status_image(status_e status);
      status_image = "?";
      case (status)
         ACK  : status_image = "ACK";
         NAK  : status_image = "NAK";
         RETRY: status_image = "RETRY";
      endcase
   endfunction: status_image
endclass: transaction
`vmm_channel(transaction)


class transaction_resp extends vmm_data;

   static vmm_log log = new("transaction_resp", "class");

   transaction req;

   bit [7:0] data;
   transaction::status_e status;

   function new(transaction tr);
      super.new(this.log);

      this.req       = tr;

      this.data_id   = tr.data_id;
      this.data      = tr.data;
      this.status    = tr.status;
   endfunction: new

   virtual function string psdisplay(string prefix = "");
      psdisplay = $psprintf("%s%s --> 'h%2h (%s)",
                            prefix, this.req.psdisplay(), data,
                            status_image(status));
   endfunction: psdisplay

   virtual function string status_image(transaction::status_e status);
      status_image = "?";
      case (status)
         transaction::ACK  : status_image = "ACK";
         transaction::NAK  : status_image = "NAK";
         transaction::RETRY: status_image = "RETRY";
      endcase
   endfunction: status_image
endclass: transaction_resp
`vmm_channel(transaction_resp)


`endif
