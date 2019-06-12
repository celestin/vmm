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

module memsys(clk, reset, busAddr, busData, busRdWr_N, adxStrb, request, grant);

input clk, reset, busRdWr_N, adxStrb;
input [7:0] busAddr;
input [1:0] request;
output [1:0] grant;
inout [7:0] busData;

wire [5:0] ramAddr;
wire [7:0] ramData;
wire rdWr_;

cntrlr Umem(clk, reset, busAddr, busData, busRdWr_N, adxStrb, rdWr_,ce0_,
         ce1_, ce2_, ce3_, ramAddr, ramData);

arb Urrarb(clk, reset, request, grant) ;

sram u0(ce0_, rdWr_, ramAddr, ramData);
sram u1(ce1_, rdWr_, ramAddr, ramData);
sram u2(ce2_, rdWr_, ramAddr, ramData);
sram u3(ce3_, rdWr_, ramAddr, ramData);

initial 
begin
//   $display("reset, request, grant, adxStrb, busAddr, busData, rdWr_");
//   $monitor($time," %b %b %b %b %h %h %b",reset, request, grant, adxStrb, busAddr, busData, busRdWr_);
end

endmodule
