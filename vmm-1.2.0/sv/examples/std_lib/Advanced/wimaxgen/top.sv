/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`define VMM_12


program P;
`include "vmm.sv"
`include "phy_env.sv"
`include "test1.sv"
`include "test2.sv"

   // external constraints are shared across tests
   constraint phy_tb_config::cst_user {
      num_of_frames == 1;
   }

   test1 t1;
   test2 t2;

   initial begin
      phy_env env;
      env = new("env");
      t1 = new("test1");
      t2 = new("test2");
      vmm_simulation::run_tests();
   end
endprogram
