//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

`ifndef BUS_SLAVE__SV
`define BUS_SLAVE__SV

`include "vmm.sv"
`include "bus_tr.sv"

class bus_slave extends vmm_xactor;

   int unsigned max_latency = 1;

   bus_tr_channel in_chan;

   function new(string         name,
                int            stream_id   = -1,
                bus_tr_channel in_chan     = null,
                int unsigned   max_latency = 1);
      super.new("Bus Slave", name, stream_id);
      this.max_latency = max_latency;

      if (in_chan == null) in_chan = new("Bus Slave Input Channel", name);
      this.in_chan = in_chan;
   endfunction: new

   virtual task main();
      super.main();

      forever begin
         bus_tr tr;

         this.wait_if_stopped_or_empty(this.in_chan);
         this.in_chan.activate(tr);

         `vmm_trace(log, $psprintf("Responding to %s", tr.psdisplay()));

         void'(this.in_chan.start());

         #(1 + $random() % max_latency);

         void'(this.in_chan.complete());

         `vmm_trace(log, $psprintf("Completed %s", tr.psdisplay()));

         void'(this.in_chan.remove());
      end
   endtask: main
endclass: bus_slave

`endif
