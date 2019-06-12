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

`include "vmm.sv"
`include "phy_tb_config.sv"
`include "phy_color.sv"
`include "phy_burst.sv"
`include "phy_zone.sv"
`include "phy_super_zone.sv"
`include "phy_frame.sv"
`include "phy_generator.sv"


class phy_env extends vmm_group;

 phy_tb_config phy_cfg;
 phy_generator phy_gen;

  function new(string inst, vmm_group parent = null);
    super.new(get_typename(), inst, parent);
  endfunction

  // build occurs in pre-test phase, only once
  virtual function void build_ph();
     phy_cfg = new("phy_cfg_inst_string_name", this);
     phy_gen = new("phy_gen", this);
  endfunction

endclass

