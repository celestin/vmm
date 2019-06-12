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

package env_pkg;
`include "vmm.sv"
class trans extends vmm_data;
   static vmm_log log = new("my_trans", "class");

   function new();
     super.new(log);
   endfunction

   virtual function void hello();
      `vmm_note(log, "Hello from 'trans'");
   endfunction
endclass

class my_env extends vmm_env;
   trans trans_obj;
   vmm_timeline my_tml;      //Instance of timeline to co-ordinate all the phases of components


   function new();
      trans_obj = new();
   endfunction

  function void build();
     super.build();
     my_tml = new("timeline","my_tml",this);
  endfunction

   task reset_dut();
     super.reset_dut();
     my_tml.run_phase("connect");
     `vmm_note(log,"Resetting the DUT");
     my_tml.run_phase("reset");
     my_tml.run_phase("training");
   endtask

   task cfg_dut();
      super.cfg_dut();
     `vmm_note(log,"Configuring the DUT");
     my_tml.run_phase("config_dut");
   endtask : cfg_dut


   task start();
      super.start();
      trans_obj.hello();
      my_tml.run_phase("start");
      my_tml.run_phase("start_of_test");
      my_tml.run_phase("run_test");

   endtask
endclass

endpackage


