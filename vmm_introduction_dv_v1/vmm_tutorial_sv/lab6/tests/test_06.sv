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
// Filename    : $Id: test_06.sv,v 1.9 2006/06/05 14:56:40 kevork Exp $
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
`include "dut_env.sv"
  
  dut_env env;                     // DUT Environment

  initial begin
    env = new(ifcmas,ifcmon);                   // Create the environment
    env.build();                   // Build the environment 
    env.run();                     // Run all steps
  end 

endprogram


