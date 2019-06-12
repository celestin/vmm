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

class GenCovCallbacks extends Packet_atomic_gen_callbacks;

  bit[3:0] sa, da;

  covergroup gen_port_cov;
    coverpoint sa;
    coverpoint da;
    cross sa, da;
    option.weight = 0;
  endgroup

  function new();
    gen_port_cov = new();
  endfunction

  virtual task post_inst_gen(Packet_atomic_gen gen, Packet obj, ref bit drop);
    this.sa = obj.sa;
    this.da = obj.da;
    gen_port_cov.sample();
  endtask

endclass
