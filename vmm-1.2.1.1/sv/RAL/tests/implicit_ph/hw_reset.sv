// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
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


`ifndef VMM_RAL_TEST_PRE_INCLUDE
`define VMM_RAL_TEST_PRE_INCLUDE ral_env.svh
`endif

`include "RAL/vmm_ral.sv"

`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_PRE_INCLUDE)


`ifndef RAL_TB_ENV
`define RAL_TB_ENV tb_env
`endif


program hw_reset;

`ifdef VMM_RAL_TEST_POST_INCLUDE
`include `VMM_MACRO_TO_STRING(`VMM_RAL_TEST_POST_INCLUDE)
`endif

typedef class `RAL_TB_ENV;


class ral_test_env extends vmm_timeline;
   `RAL_TB_ENV dut_env;

   vmm_ral_block_or_sys rals[$];

   function new();
      super.new("RAL Test Env", "ral_test", null);
   endfunction

   virtual function void build_ph();
      super.build_ph();

      this.dut_env = new(this, "dut_env");
   endfunction

   virtual function void start_of_sim_ph();
      vmm_ral_block_or_sys ral;

      //
      // Execute this test on all root RAL models found
      //
      int n_roots = vmm_object::get_num_roots();

      for (int i = 0; i < n_roots; i++) begin
         vmm_object root = vmm_object::get_nth_root(i);
         
         if ($cast(ral, root)) this.rals.push_back(ral);
      end

      if (this.rals.size() == 0) begin
         `vmm_fatal(log, "No RAL abstraction model found");
      end
   endfunction
endclass


vmm_log log = new("HW Reset", "Test");
ral_test_env ral_test;


initial
begin
   ral_test = new();

   ral_test.run_phase("reset");
   // Test each block in turn

   foreach (ral_test.rals[i]) begin
      vmm_ral_block blk;

      if ($cast(blk, ral_test.rals[i])) begin
         // Blocks with some attributes are not to be tested
         if (blk.get_attribute("NO_RAL_TESTS") == "" &&
             blk.get_attribute("NO_HW_RESET_TEST") == "") begin
            
            blk.reset();
            vmm_ral_tests::hw_reset(blk, "", log);
         end
      end
      else begin
         vmm_ral_sys   sys;
         vmm_ral_block blks[];
         string        domains[];

         $cast(sys, ral_test.rals[i]);
         sys.get_all_blocks(blks, domains);
         foreach (blks[j]) begin

            // Blocks with some attributes are not to be tested
            if (blks[j].get_attribute("NO_RAL_TESTS") != "" ||
                blks[j].get_attribute("NO_HW_RESET_TEST") != "") continue;
         
            blks[j].reset();
            vmm_ral_tests::hw_reset(blks[j], domains[j], log);
         end
      end
   end
   
   log.report();
end
endprogram: hw_reset
