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





// this test shows the directed testing.
// override_with_new is used in start_of_sim_ph() since existing scenario has to be
// replaced in the MSS generator


class cpu_directed_scenario extends cpu_rand_scenario;
   `vmm_typename(cpu_directed_scenario)

    vmm_channel chan;
   
   `vmm_scenario_new(cpu_directed_scenario)
   `vmm_scenario_member_begin(cpu_directed_scenario)
   `vmm_scenario_member_end(cpu_directed_scenario)

   task read(bit [31:0] addr,ref bit [7:0] data);
      cpu_trans tr = new();
      tr.randomize() with { tr.address == addr; tr.kind == READ;};
      chan.put(tr);
      data = tr.data;
   endtask

   task write(input bit [31:0] addr,input bit [7:0] data1);
       cpu_trans tr = new();
       tr.randomize() with { tr.address == addr; tr.kind == WRITE;tr.data == data1;};
       chan.put(tr);
   endtask

   task execute(ref int n);
      bit [7:0] data;
      if (chan == null) chan = get_channel("cpu_chan");
      this.write('h1111_1111,'h2a);
      this.read('h2222_2222,data);
      this.write('h3333_3333,'h1a);
      this.read('h5555_5555,data);
      this.read('h7777_7777,data);
   endtask
`vmm_class_factory(cpu_directed_scenario)
endclass


class test_directed extends vmm_test;
 `vmm_typename(test_directed);

   function new(string name);
      super.new(name);
   endfunction

   function void build_ph();
      vmm_opts::set_int("%*:num_scenarios", 2);
   endfunction

   function void configure_test_ph();
      cpu_rand_scenario::override_with_new("@%*:CPU:rand_scn", cpu_directed_scenario::this_type(), log, `__FILE__, `__LINE__);

   endfunction

endclass

test_directed tst_directed = new("test_directed");
