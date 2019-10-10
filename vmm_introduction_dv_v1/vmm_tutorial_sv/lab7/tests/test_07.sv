//-----------------------------------------------------------------------------
//
// SYNOPSYS CONFIDENTIAL - This is an unpublished, proprietary work of
// Synopsys, Inc., and is fully protected under copyright and trade secret
// laws. You may not view, use, disclose, copy, or distribute this file or
// any information contained herein except pursuant to a valid written
// license from Synopsys.
//
//-----------------------------------------------------------------------------
//
// Filename    : $Id: test_07.sv,v 1.9 2006/06/05 14:56:40 kevork Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: kevork $
//
// Description : Simple Test, run all steps
//
//-----------------------------------------------------------------------------


program test(apb_if.Master ifcmas, apb_if.Monitor ifcmon);

`include "vmm.sv"
`include "apb_cfg.sv"
`include "apb_trans.sv"
`include "apb_master.sv"
`include "dut_scb.sv"
`include "apb_monitor.sv"
`include "scb_callbacks.sv"
`include "cov_callbacks.sv"
`include "dut_env.sv"
  
// Lab7 - Create a constrained apb_trans class called my_abp_trans
// Lab7 - class my_apb_trans extends apb_trans;
// Lab7 -   constraint lab7 {
// Lab7 -    addr inside {0, 100, 1024};
// Lab7 -    data inside {0, 100, 1024};
// Lab7 -   }
// Lab7 - endclass






   
  dut_env env;                     // DUT Environment

  initial begin
    env = new(ifcmas,ifcmon);                   // Create the environment
    env.build();                   // Build the environment
// Lab7 - Create an my_apb_trans object.  trans = new
// Lab7 - Place the trans into the apb atomic generator (gen) object
// Lab7 - begin
// Lab7 -   my_apb_trans trans = new();
// Lab7 -   env.gen.randomized_obj = trans;
// Lab7 - end





    env.run();                     // Run all steps
  end 

endprogram


