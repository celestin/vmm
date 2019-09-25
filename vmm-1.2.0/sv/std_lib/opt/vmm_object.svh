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

`ifndef VMM_OBJECT__SVH
`define VMM_OBJECT__SVH

`ifndef VMM_DATA_BASE
   `define VMM_DATA_BASE        vmm_object
`endif
`ifndef VMM_CONSENSUS_BASE
   `define VMM_CONSENSUS_BASE   vmm_object
`endif
`ifndef VMM_NOTIFY_BASE
   `define VMM_NOTIFY_BASE      vmm_object
`endif
`ifndef VMM_XACTOR_BASE
        `define VMM_XACTOR_BASE      vmm_unit
`endif
`ifndef VMM_SUBENV_BASE
    `ifdef VMM_12_UNDERPIN_VMM_SUBENV
        `define VMM_SUBENV_BASE      vmm_unit
     `else
        `define VMM_SUBENV_BASE      vmm_object
     `endif
`endif
`ifndef VMM_CHANNEL_BASE
    `ifdef VMM_12_UNDERPIN_VMM_CHANNEL
        `define VMM_CHANNEL_BASE      vmm_unit
     `else
        `define VMM_CHANNEL_BASE      vmm_object
     `endif
`endif
`ifndef VMM_ENV_BASE
    `ifdef VMM_12_UNDERPIN_VMM_ENV
        `define VMM_ENV_BASE      vmm_timeline
     `else
        `define VMM_ENV_BASE      vmm_object
     `endif
`endif
`ifndef VMM_TEST_BASE
    `ifdef VMM_12_UNDERPIN_STDLIB
        `define VMM_TEST_BASE      vmm_timeline
     `endif
`endif

`endif // VMM_OBJECT__SVH
