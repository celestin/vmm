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

class memsys_xactor extends vmm_group;
   memsys_trans_channel genToXtr_chan;
   cpu_trans_channel    xtrToCPU0Drv_chan;
   cpu_trans_channel    xtrToCPU1Drv_chan;
   memsys_trans  mem_tr;

   function new(string name, string inst,
                vmm_group parent=null
               );
      super.new(name, inst, parent);
   endfunction

   task run_ph();
      fork
      while (1) begin
         genToXtr_chan.peek(mem_tr);
         genToXtr_chan.get(mem_tr);
         
         
         case(mem_tr.cpuid)
            0: xtrToCPU0Drv_chan.put(mem_tr);
            1: xtrToCPU1Drv_chan.put(mem_tr);
            default: `vmm_error(log, "illegal CPU Id generated");
         endcase
      end
      join_none
      #10;
   endtask
endclass
