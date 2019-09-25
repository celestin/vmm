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

   function new(transaction_channel in_chan = null);
      super.new("Consumer", "In-Order");

      // Example 4-65
      if (in_chan == null) in_chan = new("Input Channel", "Consumer");
      in_chan.reconfigure(1);
      this.in_chan = in_chan;
   endfunction: new

   virtual task main();
      bit [7:0] ram [4];

      for(int i = 0; i < $size(ram); i++) begin
         ram[i] = {i << 4, 4'hF};
      end
          
      fork
         super.main();
      join_none

      forever begin
         transaction tr;
         bit [1:0] p;

         // Example 4-66
         // Example 4-67
         this.in_chan.peek(tr);
         tr.notify.indicate(vmm_data::STARTED);
         
         `vmm_note(this.log, tr.psdisplay("Executing: "));
         #(10);
         
         if (tr.kind == transaction::READ) tr.data = 8'hXX;
         p = $random;
         case (p)
            0,1: begin
                  tr.status = transaction::ACK;
                  case (tr.kind)
                     transaction::READ : tr.data = ram[tr.addr];
                     transaction::WRITE: ram[tr.addr] = tr.data;
                  endcase
               end
            2: tr.status = transaction::NAK;
            3: tr.status = transaction::RETRY;
         endcase
         `vmm_note(this.log, tr.psdisplay("Completed: "));

         // Example 4-67
         begin
            transaction_resp tr_status = new(tr);
            tr.notify.indicate(vmm_data::ENDED, tr_status );
         end

         // Example 4-66
         this.in_chan.get(tr);
      end
   endtask: main
endclass: consumer
