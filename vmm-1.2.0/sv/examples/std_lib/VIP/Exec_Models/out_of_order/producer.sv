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

   integer DONE;

   function new(transaction_channel out_chan = null);
      super.new("Producer", "Nonblocking");

      if (out_chan == null) out_chan = new("Output Channel", "Producer");
      this.out_chan = out_chan;

      this.DONE = this.notify.configure(.sync(vmm_notify::ON_OFF));
   endfunction: new

   virtual task main();
      integer n = 0;
      integer c = 0;

      fork
         super.main();
      join_none

      repeat (10) begin
         transaction tr = new;

         tr.data_id = n++;
         void'(tr.randomize());

         // Example 4-71
         `vmm_note(this.log, tr.psdisplay("Requesting: "));
         out_chan.put(tr);

         fork
            begin
               automatic transaction w4tr = tr;
               w4tr.notify.wait_for(vmm_data::ENDED);
               `vmm_note(this.log, tr.psdisplay("Completion: "));
               c++;
               if (c == 10) this.notify.indicate(this.DONE);
            end
         join_none
      end

   endtask: main
endclass: producer
