//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "transaction.sv"

class responder extends vmm_xactor;
   transaction_resp_channel req_chan;
   transaction_resp_channel resp_chan;

   function new(transaction_resp_channel req_chan  = null,
                transaction_resp_channel resp_chan = null);
      super.new("Responder", "Reactive");

      if (req_chan == null) req_chan = new("Request Channel", "Responder");
      this.req_chan = req_chan;

      if (resp_chan == null) resp_chan = new("Response Channel", "Responder");
      this.resp_chan = resp_chan;
   endfunction: new

   virtual task main();
      integer response_id = 0;

      fork
         super.main();
      join_none

      forever begin
         transaction_resp tr;

         this.req_chan.get(tr);
         tr.notify.indicate(vmm_data::STARTED);
         `vmm_note(this.log, tr.psdisplay("Responding to: "));
         
         #3; // Ideally, should respond in zero-time

         // Example 4-80
         // Generate a random response
         tr.stream_id = this.stream_id;
         tr.data_id   = response_id++;
         if (!tr.randomize()) begin
            `vmm_fatal(this.log, "Unable to generate random response");
         end
         
         tr.notify.indicate(vmm_data::ENDED);
         this.resp_chan.sneak(tr);
         
         `vmm_note(this.log, tr.psdisplay("Responded with: "));
      end
   endtask: main
endclass: responder
