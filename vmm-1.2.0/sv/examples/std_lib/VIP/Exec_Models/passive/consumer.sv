//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "transaction.sv"

class consumer extends vmm_xactor;
   transaction_channel in_chan;

   integer DONE;

   function new(transaction_channel in_chan = null);
      super.new("Consumer", "Passive");

      if (in_chan == null) in_chan = new("Input Channel", "Consumer");
      this.in_chan = in_chan;

      this.DONE = this.notify.configure(.sync(vmm_notify::ON_OFF));
   endfunction: new

   virtual task main();
      fork
         super.main();
      join_none

      repeat (10) begin
         transaction tr;

         // Example 4-77
         this.in_chan.peek(tr);
         `vmm_note(this.log, tr.psdisplay("Started: "));
         tr.notify.wait_for(vmm_data::ENDED);
         `vmm_note(this.log, tr.psdisplay("Completed: "));
         this.in_chan.get(tr);
      end

      this.notify.indicate(this.DONE);

   endtask: main
endclass: consumer
