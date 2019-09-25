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

/***************************************************************************
*******************************************************************************
*
* Class retaining all configuration parameters
* that do pertain to the FPU from open cores
*
*******************************************************************************
*/

`ifndef _FPU_CFG_SV
`define _FPU_CFG_SV

class fpu_cfg ;
  
  // Maximum number of transactions
  rand int max_trans_cnt;

  // basic constraint applied to max_trans_cnt
  constraint basic {
    (max_trans_cnt > 0) && (max_trans_cnt < 10);
  }
endclass: fpu_cfg

`endif
