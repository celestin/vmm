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

interface sram_if (input bit clk,
                   input bit      ce_N,
                   input bit      rdWr_N,
                   input bit[31:0] ramAddr,
                   inout [7:0] ramData);

  clocking cb @(posedge clk);
    input #1 ce_N;
    input #1 rdWr_N;
    input ramAddr;
    inout ramData;
  endclocking

  modport memprt(input ramAddr, inout ramData, input ce_N, input rdWr_N, clocking cb);
  modport monprt(input ramAddr, input ramData, input ce_N, input rdWr_N, clocking cb);
endinterface

