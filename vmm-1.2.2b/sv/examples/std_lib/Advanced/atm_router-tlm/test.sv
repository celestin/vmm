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

`timescale 1ns/100ps
`include "vmm.sv"
`include "Environment.sv"

class newPacket extends Packet;
  Configuration cfg;
  constraint test {
    payload.size inside { [2:4] };
    sa inside cfg.valid_iports;
    da inside cfg.valid_oports;
  }
  function new(Configuration cfg);
    this.cfg = cfg;
  endfunction
  function void post_randomize();
    super.post_randomize();
    `vmm_debug(this.log, this.psdisplay());
  endfunction
endclass

program automatic test(router_io.TB router);
initial begin
  Environment env = new(router);
  newPacket pkt;
  env.cfg.run_for_n_packets.rand_mode(0);
  env.cfg.num_of_iports.rand_mode(0);
  env.cfg.num_of_oports.rand_mode(0);
  env.cfg.run_for_n_packets = 0;
  env.cfg.num_of_iports = 16;
  env.cfg.num_of_oports = 16;
  env.gen_cfg();
  env.cfg.display();
  env.build();
  foreach(env.gen[i]) begin
     pkt = new(env.cfg);
     env.gen[i].randomized_obj = pkt;
  end
  env.run();
end
endprogram

