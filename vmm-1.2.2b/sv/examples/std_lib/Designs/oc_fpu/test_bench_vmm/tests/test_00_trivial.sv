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
* This test shows how to run a trivial test
* to debug the environment and the DUT
*
*******************************************************************************
*/


program test (fpu_i iport);

`include "vmm.sv"
`include "fpu.sv"
`include "env.sv"

    // Top level environment
    env the_env = new(iport);

    initial begin
   
       //the_env.log.set_verbosity(the_env.log.TRACE_SEV);

       // Run for only 1 scenario
       the_env.gen_cfg();
       the_env.cfg.run_for = 1000;

       // Kick off the test
        the_env.run();
    end

endprogram
