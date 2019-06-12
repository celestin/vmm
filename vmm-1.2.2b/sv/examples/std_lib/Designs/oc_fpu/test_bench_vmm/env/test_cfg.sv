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

//
// Test configuration descriptor
//

`ifndef _TEST_CFG_SV_
`define _TEST_CFG_SV_

typedef class fpu_cfg;

class test_cfg ;
   rand int run_for;
   rand fpu_cfg fpu;

   constraint test_cfg1 {
      run_for > 0;
   }

   constraint reasonable {
      run_for < 50;
   }

   function new() ;
      this.fpu = new;
   endfunction: new
endclass: test_cfg

`endif
