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
// Note that override_with_new is called before transaction::create_instance is
// called inside the scenario blueprint
// ie., override_with... method 


class test_write_back2back_test_trans extends cpu_trans;
   //Macros which define utility methods like copy, allocatte, etc
  `vmm_data_member_begin(test_write_back2back_test_trans)
  `vmm_data_member_end(test_write_back2back_test_trans)

  constraint cst_dly {
     kind == WRITE;
     trans_delay == 0;
  }

  `vmm_class_factory(test_write_back2back_test_trans)
endclass

class test_write_back2back extends vmm_test;
  `vmm_typename(test_write_back2back)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void configure_test_ph();
     cpu_trans::override_with_new("@%*", test_write_back2back_test_trans::this_type(), log, `__FILE__, `__LINE__);
  endfunction

  virtual function void build_ph();
     vmm_opts::set_int("%*:num_scenarios", 50);
  endfunction


endclass
test_write_back2back t_write_back2back = new("test_write_back2back");
