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
   transaction_channel out_chan;

   function new(transaction_channel out_chan = null);
      super.new("Producer", "Passive");

      if (out_chan == null) out_chan = new("Output Channel", "Producer");
      this.out_chan = out_chan;
   endfunction: new

   virtual task main();
      integer n = 0;

      fork
         super.main();
      join_none

      forever begin
         transaction tr;
         bit [7:0] data;
         bit [1:0] p;

         #10; // Observed delay between transactions

         // Example 4-76
         // A new transaction is being observed
         tr = new;
         tr.data_id = n++;

         // Fill in what we already know about the transaction
         tr.randomize();
         data = tr.data;
         tr.data = 8'hXX;
         
         tr.notify.indicate(vmm_data::STARTED);
         this.out_chan.sneak(tr);
         `vmm_note(this.log, tr.psdisplay("Observing: "));
         
         #(10); // Execution time

         // Complete transaction information, as we observe
         if (tr.kind == transaction::WRITE) tr.data = data;
         p = $random;
         case (p)
            0,1: begin
                  tr.data = data;
                  tr.status = transaction::ACK;
               end
            2: tr.status = transaction::NAK;
            3: tr.status = transaction::RETRY;
         endcase
         tr.notify.indicate(vmm_data::ENDED);
         `vmm_note(this.log, tr.psdisplay("Observed: "));
      end
   endtask: main
endclass: producer
