/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`include "vmm.sv"
`include "phy_tb_config.sv"
`include "phy_color.sv"
`include "phy_burst.sv"
`include "phy_zone.sv"
`include "phy_super_zone.sv"
`include "phy_frame.sv"
`include "phy_generator.sv"


class phy_env extends vmm_unit;

 phy_tb_config phy_cfg;
 phy_generator phy_gen;

  function new(string inst, vmm_unit parent = null);
    super.new(get_typename(), inst, parent);
  endfunction

  // build occurs in pre-test phase, only once
  virtual function void build_ph();
     phy_cfg = new("phy_cfg_inst_string_name", this);
     phy_gen = new("phy_gen", this);
  endfunction

endclass

