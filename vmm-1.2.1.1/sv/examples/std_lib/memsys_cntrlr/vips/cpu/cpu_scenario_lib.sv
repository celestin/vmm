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

class cpu_rand_scenario extends vmm_ms_scenario;
  cpu_trans       blueprint;
 `vmm_scenario_new(cpu_rand_scenario)

 `vmm_scenario_member_begin(cpu_rand_scenario)
  `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
 `vmm_scenario_member_end(cpu_rand_scenario)

  function new();
     blueprint = cpu_trans::create_instance(this, "blueprint", `__FILE__, `__LINE__);
  endfunction

  virtual task execute(ref int n);
     cpu_trans tr;
     bit res;
     vmm_channel chan;
     if (chan == null) chan = get_channel("cpu_chan");
     $cast(tr, blueprint.copy());
     res = tr.randomize();
     chan.put(tr);
  endtask

  `vmm_class_factory(cpu_rand_scenario)
endclass


class cpu_write_scenario extends cpu_rand_scenario;
  rand bit [7:0] data;
  rand bit [31:0] addr;
 `vmm_scenario_new(cpu_write_scenario)

 `vmm_scenario_member_begin(cpu_write_scenario)
  `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
  `vmm_scenario_member_scalar(data, DO_ALL) 
  `vmm_scenario_member_scalar(addr, DO_ALL) 
 `vmm_scenario_member_end(cpu_write_scenario)

  virtual task execute(ref int n);
     cpu_trans tr;
     bit res;
     vmm_channel chan;
     if (chan == null) chan = get_channel("cpu_chan");
     $cast(tr, blueprint.copy());
     res = tr.randomize() with {
       kind == WRITE;
       address == addr;
     };
     tr.data = data;
     chan.put(tr);
  endtask

  `vmm_class_factory(cpu_write_scenario)
endclass

class cpu_read_scenario extends cpu_rand_scenario;
  rand bit [7:0] data;
  rand bit [31:0] addr;
 `vmm_scenario_new(cpu_read_scenario)

 `vmm_scenario_member_begin(cpu_read_scenario)
  `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
  `vmm_scenario_member_scalar(data, DO_ALL) 
  `vmm_scenario_member_scalar(addr, DO_ALL) 
 `vmm_scenario_member_end(cpu_read_scenario)

  virtual task execute(ref int n);
     cpu_trans tr;
     bit res;
     vmm_channel chan;
     if (chan == null) chan = get_channel("cpu_chan");
     $cast(tr, blueprint.copy());
     res = tr.randomize() with {
       kind == READ;
       address == addr;
     };
     chan.put(tr);
     data = tr.data;
  endtask

  `vmm_class_factory(cpu_read_scenario)
endclass


class cpu_write_read_same_addr_scenario extends cpu_rand_scenario;
 cpu_write_scenario  write_scn;
 cpu_read_scenario   read_scn;
 rand bit [31:0]     Addr;
 rand bit [7:0]      Data;

 `vmm_scenario_new(cpu_write_read_same_addr_scenario)

 `vmm_scenario_member_begin(cpu_write_read_same_addr_scenario)
  `vmm_scenario_member_vmm_scenario(write_scn, DO_ALL)
  `vmm_scenario_member_vmm_scenario(read_scn, DO_ALL)
  `vmm_scenario_member_scalar(Data, DO_ALL) 
  `vmm_scenario_member_scalar(Addr, DO_ALL) 
 `vmm_scenario_member_end(cpu_write_read_same_addr_scenario)

  function new();
     write_scn = cpu_write_scenario::create_instance(this, "write_scn", `__FILE__, `__LINE__);
     read_scn = cpu_read_scenario::create_instance(this, "read_scn", `__FILE__, `__LINE__);
     write_scn.set_parent_scenario(this);
     read_scn.set_parent_scenario(this);
  endfunction

  virtual task execute(ref int n);
     cpu_trans tr;
     bit res;
     vmm_channel chan;
     write_scn.randomize() with {addr == this.Addr; data == this.Data;};
     write_scn.execute(n);
     read_scn.randomize() with {addr == this.Addr;};
     read_scn.execute(n);
  endtask

  `vmm_class_factory(cpu_write_read_same_addr_scenario)

endclass

class cpu_write_word_scenario extends cpu_rand_scenario;
  rand bit [7:0] data;
  rand bit [31:0] addr;
 `vmm_scenario_new(cpu_write_word_scenario)

 `vmm_scenario_member_begin(cpu_write_word_scenario)
  `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
  `vmm_scenario_member_scalar(data, DO_ALL) 
  `vmm_scenario_member_scalar(addr, DO_ALL) 
 `vmm_scenario_member_end(cpu_write_word_scenario)


  virtual task execute(ref int n);
     cpu_trans tr;
     bit res;
     vmm_channel chan;
     if (chan == null) chan = get_channel("cpu_chan");
     for (int i=0; i<4; i++) begin
        $cast(tr, blueprint.copy());
        res = tr.randomize() with {
          kind == WRITE;
          address == addr + i;
        };
        tr.data = data >> i * 8;
        chan.put(tr);
     end
  endtask

  `vmm_class_factory(cpu_write_word_scenario)
endclass

