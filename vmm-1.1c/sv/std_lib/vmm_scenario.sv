// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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
// This file was modified by Mentor Graphics. See QUESTA.html
// in root directory for details.



function vmm_scenario::new(`VMM_LOG log `VMM_SCENARIO_NEW_ARGS);
   super.new(log `VMM_SCENARIO_NEW_CALL);
endfunction: new


function string vmm_scenario::psdisplay(string prefix = "");
   int i;

   $sformat(psdisplay,
            "%sScenario \"%s\": kind=%0d, length=%0d (max=%0d), repeated=%0d",
            prefix, this.scenario_name(this.scenario_kind),
            this.scenario_kind, this.length, this.max_length,
            this.repeated);
endfunction: psdisplay


function int unsigned vmm_scenario::define_scenario(string name,
                                                    int unsigned max_len);
   define_scenario = this.next_scenario_kind++;
   this.scenario_names[define_scenario] = name;

   if (max_len > this.max_length) this.max_length = max_len;
endfunction: define_scenario


function void vmm_scenario::redefine_scenario(int unsigned scenario_kind,
                                              string       name,
                                              int unsigned max_len);
   this.scenario_names[scenario_kind] = name;
    if (max_len > this.max_length) this.max_length = max_len;
endfunction: redefine_scenario


function string vmm_scenario::scenario_name(int unsigned scenario_kind);
   if (!this.scenario_names.exists(scenario_kind)) begin
      `vmm_error(super.notify.log, `vmm_sformatf("Cannot find scenario name: undefined scenario kind %0d",
                                         scenario_kind));
      return "?";
   end

   scenario_name = this.scenario_names[scenario_kind];
endfunction: scenario_name


function int unsigned vmm_scenario::get_max_length();
   return this.max_length;
endfunction: get_max_length

function void vmm_scenario::set_parent_scenario(vmm_scenario parent);
   this.parent = parent;
   if(parent == null) return;
endfunction: set_parent_scenario

function vmm_scenario vmm_scenario::get_parent_scenario();
   get_parent_scenario = this.parent;
endfunction: get_parent_scenario

task vmm_scenario::execute(ref int n);
endtask: execute
