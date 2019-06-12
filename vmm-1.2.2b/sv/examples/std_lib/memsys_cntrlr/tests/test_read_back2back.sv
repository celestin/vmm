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





//This test demonstrates how to use transaction factory methods
// Note that override_with_copy is called before transaction::create_instance is
// called inside the scenario blueprint

class test_read_back2back_test_trans extends cpu_trans;

   //Macros which define utility methods like copy, allocatte, etc
  `vmm_data_member_begin(test_read_back2back_test_trans)
  `vmm_data_member_rand_scalar(address, DO_COPY)
  `vmm_data_member_end(test_read_back2back_test_trans)

  constraint cst_dly {
     kind == READ;
     trans_delay == 0;
  }

  `vmm_class_factory(test_read_back2back_test_trans)
endclass

class test_read_back2back extends vmm_test;

  function new(string name);
     super.new(name);
  endfunction

  virtual function void configure_test_ph();
     test_read_back2back_test_trans tr = new();
     tr.address = 'habcd_1234;
     tr.address.rand_mode(0);
     cpu_trans::override_with_copy("@%*", tr, log, `__FILE__, `__LINE__);
     vmm_opts::set_int("%*:num_scenarios", 50);
  endfunction

endclass
test_read_back2back t_read_back2back = new("test_read_back2back");
