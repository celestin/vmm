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






//the purpose of this test and test_concatenate1.sv is to demonstrate test concatenation
class test_concatenate2 extends vmm_test;
  //Macro to indicate the rollback phase in case of test concatenation
  `vmm_test_concatenate(start_of_sim)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void configure_test_ph();
     vmm_opts::set_int("%*:num_scenarios", 20);
     cpu_rand_scenario::override_with_new("@%*:CPU:rand_scn", cpu_write_scenario::this_type(), log, `__FILE__, `__LINE__);
  endfunction


endclass
test_concatenate2 t_concatenate2 = new("test_concatenate2");
