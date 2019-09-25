//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "transaction.sv"

class requestor extends vmm_xactor;
   transaction_resp_channel req_chan;
   transaction_resp_channel resp_chan;

   integer DONE;

   function new(transaction_resp_channel req_chan   = null,
                transaction_resp_channel resp_chan = null);
      super.new("Requestor", "Reactive");

      if (req_chan == null) req_chan = new("Request Channel", "Requestor");
      this.req_chan = req_chan;

      if (resp_chan == null) resp_chan = new("Response Channel", "Requestor");
      this.resp_chan = resp_chan;

      this.DONE = this.notify.configure(.sync(vmm_notify::ON_OFF));
   endfunction: new

   virtual task main();
      integer n = 0;

      fork
         super.main();
      join_none

      repeat (10) begin
         transaction      tr;
         transaction_resp resp;
         bit [7:0] data;

         #10; // Observed delay between transactions

         // A new transaction is being observed
         tr = new;

         // Fill in as much as possible before we
         // need to make a response request
         void'(tr.randomize());
         data = tr.data;
         if (tr.kind == transaction::READ) tr.data = 8'hXX;
         tr.notify.indicate(vmm_data::STARTED);

         // Example 4-78
         `vmm_note(this.log, tr.psdisplay("Requesting response to: "));
         resp = new(tr);
         this.req_chan.sneak(resp);

         // Example 4-79
         resp = null;
         fork
            this.resp_chan.get(resp);
            #(7); // Maximum response delay
         join_any
         disable fork;
         if (resp == null) begin
            // Compose a default response
            resp = new(tr);
            `vmm_warning(this.log, "Did not receive response in time");
            resp.status = transaction::NAK;
         end

         if (resp.req != tr) begin
            `vmm_fatal(this.log,
                       "Response does not correspond to transaction");
            resp = new(tr);
            resp.status = transaction::NAK;
         end

         #(3); // Complete transaction using response
         tr.notify.indicate(vmm_data::ENDED);
         `vmm_note(this.log, resp.psdisplay("Completed with: "));
      end // repeat (10)

      this.notify.indicate(DONE);
   endtask: main
endclass: requestor
