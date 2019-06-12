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

class memsys_scenario extends memsys_trans_scenario;
  int SCN_KIND = this.define_scenario("MEMSYS_SCENARIO", 2);

  constraint cst_memsys_scenario {
    repeated == 0;
    length == 2;
  }

  virtual function vmm_data allocate();
       memsys_scenario scn = new();
       return scn;
  endfunction

  virtual function vmm_data copy(vmm_data to = null);
     memsys_scenario scn = new();
     scn.SCN_KIND = this.SCN_KIND;
     copy = super.copy(scn);
  endfunction

`vmm_class_factory(memsys_scenario)
endclass



