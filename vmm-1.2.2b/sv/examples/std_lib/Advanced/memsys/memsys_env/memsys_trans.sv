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

class memsys_trans extends cpu_trans;
  rand int cpuid;

  constraint cst_id {
    cpuid inside {[0:1]};
  }

   `vmm_data_member_begin(memsys_trans)
   `vmm_data_member_scalar(cpuid, DO_ALL)
   `vmm_data_member_end(memsys_trans)

  `vmm_class_factory(memsys_trans)

endclass
`vmm_channel(memsys_trans)
`vmm_scenario_gen(memsys_trans, "MEMSYS scenario generator")

