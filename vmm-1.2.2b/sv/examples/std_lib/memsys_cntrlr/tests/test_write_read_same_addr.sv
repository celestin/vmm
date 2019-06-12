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





//This test demostrates usage for factory for multi stream scenario
// Note that override_.. method is called after the scenario is created

class test_write_read_same_addr extends vmm_test;
  `vmm_typename(test_write_read_same_addr)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void build_ph();
    vmm_opts::set_int("%*:num_scenarios", 20);
  endfunction

  virtual function void configure_test_ph();
     cpu_rand_scenario::override_with_new("@%*:CPU:rand_scn", cpu_write_read_same_addr_scenario::this_type(), log, `__FILE__, `__LINE__);
  endfunction

endclass
test_write_read_same_addr t_write_read_same_addr = new("test_write_read_same_addr");
