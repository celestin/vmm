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





//This test shows how to do error injection using callbacks
// Assuming 'hdead_dead is a corrupt address, transactions are corrupted with
// the address before driven by the cpu_driver
// Note that callback object is prepended to make sure that the corrupted address
//  is available for other callback instances if any

class test_error_callback extends cpu_driver_callbacks;

   virtual task pre_trans(cpu_driver drv, cpu_trans tr,ref bit drop);
      tr.address = 'hdead_dead;
   endtask

endclass

class test_error extends vmm_test;
   

   function new(string name );
      super.new(name);
   endfunction 

   virtual function void build_ph();
      vmm_opts::set_int("%*:num_scenarios", 5);
   endfunction 

   virtual function void configure_test_ph();
      test_error_callback t_cb = new;
      env.cpu.drv.prepend_callback(t_cb);
   endfunction

endclass


test_error t_error = new("test_error");
