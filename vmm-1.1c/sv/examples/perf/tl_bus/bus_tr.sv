// 
// -------------------------------------------------------------
//    Original had no Synopsys copyright
//    Copyright 2009 Mentor Graphics Corporation
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
// This file was modified by Mentor Graphics. See QUESTA.html
// in root directory for details.

`ifndef BUS_TR__SV
`define BUS_TR__SV

`include "vmm.sv"

class bus_tr extends vmm_data;

   static vmm_log log = new("bus_tr", "class");

   rand enum {READ, WRITE} kind;
   rand bit [31:0] addr;
   rand bit [31:0] data;
   rand enum {UNKNOWN, IS_OK, RETRY, ABORT, TIMEOUT} status;

   constraint bus_tr_valid {
      status != UNKNOWN;
   }

   function new();
      super.new(this.log);
   endfunction: new

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%s%s cycle @ 0x%h = 0x%h [%s]", prefix,
               this.kind.name(), this.addr, this.data, this.status.name());
   endfunction: psdisplay

   virtual function bit is_valid(bit     silent = 1,
                                 input int kind   = -1);
      return 1;
   endfunction: is_valid

   virtual function vmm_data allocate();
      bus_tr tr = new;
      return tr;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data to = null);
      bus_tr to_i;

      if (to == null) to_i = new;
      else if (!$cast(to_i, to)) begin 
         `vmm_fatal(this.log, "Attempting to copy to a non-bus_tr instance");
          return null;
      end 

      super.copy_data(to_i);

      to_i.kind   = this.kind;
      to_i.addr   = this.addr;
      to_i.data   = this.data;
      to_i.status = this.status;

      return to_i;     
   endfunction: copy

   virtual function bit compare(vmm_data   to,
                                output string diff,
                                input int  kind = -1);
      bus_tr tr;
       
      if (to == null) begin 
         `vmm_fatal(this.log, "Cannot compare to NULL instance");
         return 0;
      end

      if (!$cast(tr,to)) begin 
         `vmm_fatal(this.log, "Attempting to compare to a non-bus_tr instance");
         return 0;
      end

      if (this.kind != tr.kind) begin
         $sformat(diff, "Kind %s != %s", this.kind.name(), tr.kind.name());
         return 0;
      end
      if (this.addr != tr.addr) begin
         $sformat(diff, "Addr 0x%h != 0x%h", this.addr, tr.addr);
         return 0;
      end
      if (this.data != tr.data) begin
         $sformat(diff, "Data 0x%h != 0x%h", this.data, tr.data);
         return 0;
      end
      if (this.status != tr.status) begin
         $sformat(diff, "Status 0x%h != 0x%h", this.status.name(),
                  tr.status.name());
         return 0;
      end

      return 1;
   endfunction: compare

endclass: bus_tr

`vmm_channel(bus_tr)
`vmm_atomic_gen(bus_tr, "Bus Cycle")
`vmm_scenario_gen(bus_tr, "Bus Cycle")

`endif
