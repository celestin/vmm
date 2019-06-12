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

interface cpu_if (input bit clk);
  wire	        busRdWr_N;
  wire	        adxStrb;
  wire [31:0]   busAddr;
  wire [ 7:0]   busData;
  wire          cpu_req;
  wire 		cpu_grant;

  clocking cb @(posedge clk);
    output busAddr;
    inout  busData;
    output adxStrb;
    output busRdWr_N;
  endclocking

  modport drvprt(clocking cb);
endinterface

