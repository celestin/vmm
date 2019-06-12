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

class test_write_memsys_scenario extends memsys_scenario;
  
  constraint tst_const {
     foreach (items[i]) {items[i].kind == cpu_trans::WRITE};
  }

  virtual function vmm_data allocate();
     test_write_memsys_scenario tst_scn = new();
     allocate = tst_scn;
  endfunction

  virtual function vmm_data copy(vmm_data to = null);
     test_write_memsys_scenario tst_scn = new;
     copy = super.copy(tst_scn);
  endfunction

endclass

class test_write extends vmm_test;
  `vmm_typename(test_write)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void set_config();
     memsys_scenario::override_with_new("@%*", test_write_memsys_scenario::this_type, log, `__FILE__, `__LINE__);  
  endfunction

  
  virtual function void build_ph();
     vmm_opts::set_int("num_scenarios", 10, this);
  endfunction

endclass
test_write tst4 = new("test_write");

