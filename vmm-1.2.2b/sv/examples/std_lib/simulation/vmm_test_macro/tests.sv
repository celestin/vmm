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

import env_pkg::*;

`vmm_test_begin(test1, my_env, "Test #1")
   `vmm_note(log, {"Starting test ", get_name()});
   this.env.run();
   `vmm_note(log, {"Done test ", get_name()});
`vmm_test_end(test1)

class my_trans extends trans;
   virtual function void hello();
      `vmm_note(log, "Hello from 'my_trans'");
   endfunction
endclass


`vmm_test_begin(test2, my_env, "Test #2")
   `vmm_note(log, {"Starting test ", get_name()});
			begin
     my_trans my_trans_obj = new;
					this.env.trans_obj = my_trans_obj;
			end
   this.env.run();
   `vmm_note(log, {"Done test ", get_name()});
`vmm_test_end(test2)
