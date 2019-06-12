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



//------------------------------------------------------------------------------
// CLASS: vmm_ral_env
// Base class, derived from vmm_env, to be used when creating RAL-based verification
// environments. This section documents only the differences or additions in this class
// in comparison to the base class. You can find the documentation for the properties and
// methods inherited as-is in the Reference Verification Methodology User's Guide and
// the Verification Methodology Manual for SystemVerilog. 
//------------------------------------------------------------------------------
class vmm_ral_env extends `VMM_ENV;
   vmm_ral_access ral;


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // Creates a new instance of a RAL-based environment base class. This method is usually
   // called by the constructor of a user-defined extension of this class using super.new().
   // 
   //------------------------------------------------------------------------------
   extern function new(string name = "RAL-Based Verif Env");

  `ifdef VMM_12_UNDERPIN_STDLIB
  `vmm_typename(vmm_ral_env)
  `endif

   //------------------------------------------------------------------------------
   // TASK: sw_reset
   // This method must be overloaded in a user-extension of this base class. It performs a
   // complete software reset of the design. The design must be in its reset state when the
   // task returns. 
   //------------------------------------------------------------------------------
   extern virtual task sw_reset(string domain = "");
endclass: vmm_ral_env


function vmm_ral_env::new(string name= "RAL-Based Verif Env");
   super.new(name);
   this.ral = new;
   this.ral.start_xactor(); // Added to start the vmm_ral_access::main()
endfunction: new


task vmm_ral_env::sw_reset(string domain = "");
endtask: sw_reset
