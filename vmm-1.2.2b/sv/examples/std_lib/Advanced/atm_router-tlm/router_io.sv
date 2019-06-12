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

`ifndef _ROUTER_IO_IF
`define _ROUTER_IO_IF
interface router_io(input bit clock);
  logic  reset_n ;
  logic [15:0] frame_n ;
  logic [15:0] valid_n ;
  logic [15:0] din ;
  logic [15:0] dout ;
  logic [15:0] busy_n ;
  logic [15:0] valido_n ;
  logic [15:0] frameo_n ;

  clocking cb @(posedge clock);
    output  reset_n;
    output  frame_n;
    output  valid_n;
    output  din;
    input  dout;
    input  busy_n;
    input  valido_n;
    input  frameo_n;
  endclocking

  modport TB(clocking cb, output reset_n);
endinterface: router_io
`endif
