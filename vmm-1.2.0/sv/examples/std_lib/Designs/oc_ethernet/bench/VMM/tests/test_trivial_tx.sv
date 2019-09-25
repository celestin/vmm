// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
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


`include "timescale.v"

`include "wb_if.sv"
`include "mii_if.sv"

// Example 4-16
program test;

`define MII_MAC_BFM__SV
`include "../tb_env.sv"

initial
begin
   tb_env env = new;

   fork
      forever begin
         @ (posedge tb_top.wb_int);
         `vmm_note(env.log, "Interrupt asserted!");
      end
   join_none

   env.gen_cfg();
   env.cfg.run_for_n_tx_frames = 3;
   env.cfg.run_for_n_rx_frames = 0;
   env.run();
end
endprogram: test
