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


class cpu_trans extends vmm_data;

   typedef enum bit {READ = 1'b1, WRITE =  1'b0} kind_e;

   rand bit [7:0] address;
   rand bit [7:0] data;
   rand kind_e    kind;
   rand int trans_delay;

   `vmm_data_member_begin(cpu_trans)
   `vmm_data_member_scalar(address, DO_ALL)
   `vmm_data_member_scalar(data, DO_ALL)
   `vmm_data_member_enum(kind, DO_ALL)
   `vmm_data_member_end(cpu_trans)

    `vmm_class_factory(cpu_trans)
endclass
`vmm_channel(cpu_trans)
`vmm_scenario_gen(cpu_trans, "CPU scenario generator")
