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

class memsys_scenario extends vmm_ms_scenario;

   cpu_scenario      cpu0_scn;
   cpu_scenario      cpu1_scn;
   semaphore         sem;

   function new();
     cpu0_scn = new;
     cpu1_scn = new;
     sem = new(1);
   endfunction

   virtual task execute(ref int n);
      cpu_trans_channel cpu0_chan;
      cpu_trans_channel cpu1_chan;
      int unsigned insts = n;
      $cast(cpu0_chan,  get_channel("cpu0_chan"));
      $cast(cpu1_chan,  get_channel("cpu1_chan"));
      fork 
        begin
          sem.get();
          void'(cpu0_scn.randomize());
          cpu0_scn.apply(cpu0_chan, insts);
          sem.put();
        end
        begin
          sem.get();
          void'(cpu1_scn.randomize());
          cpu1_scn.apply(cpu1_chan, insts);
          sem.put();
        end
      join
      n = insts;
   endtask

endclass

