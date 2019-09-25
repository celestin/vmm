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


module slave_ip(input  bit   [ 7:0] apb_addr,
                input  bit          apb_sel,
                input  bit          apb_enable,
                input  bit          apb_write,
                output bit   [15:0] apb_rdata,
                input  logic [15:0] apb_wdata,
                input  bit          clk,
                input  bit          rst);

bit [15:0] ram [0:255];

assign apb_rdata = (apb_sel && apb_enable && !apb_write) ? ram[apb_addr] : 'z;


always @ (posedge clk)
begin
   if (apb_write && apb_write && apb_sel) ram[apb_addr] = apb_wdata;
end

endmodule: slave_ip
