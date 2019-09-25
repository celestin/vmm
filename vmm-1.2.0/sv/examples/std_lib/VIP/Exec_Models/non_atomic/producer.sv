//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "transaction.sv"

class producer extends vmm_xactor;
   transaction_channel      out_chan;
   transaction_resp_channel resp_chan;

   integer DONE;

   function new(transaction_channel      out_chan   = null,
                transaction_resp_channel resp_chan = null);
      super.new("Producer", "Nonblocking");

      if (out_chan == null) out_chan = new("Request Channel", "Producer");
      this.out_chan = out_chan;

      if (resp_chan == null) resp_chan = new("Response Channel", "Consumer");
      this.resp_chan = resp_chan;

      this.DONE = this.notify.configure(.sync(vmm_notify::ON_OFF));
   endfunction: new

   virtual task main();
      integer n = 0;
      integer c = 0;

      fork
         super.main();

         repeat (10) begin
            transaction tr = new;

            tr.data_id = n++;
            void'(tr.randomize());

            `vmm_note(this.log, tr.psdisplay("Requesting: "));
            out_chan.put(tr);
         end

         begin
            repeat (10) begin
               transaction_resp resp;

               this.resp_chan.get(resp);
               `vmm_note(this.log, resp.psdisplay("Completion: "));
            end

            this.notify.indicate(DONE);
         end
      join_none
   endtask: main
endclass: producer
