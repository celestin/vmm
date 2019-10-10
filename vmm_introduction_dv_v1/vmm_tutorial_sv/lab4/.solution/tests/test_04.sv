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
// Filename    : $Id: test_04.sv,v 1.6 2006/06/05 14:56:40 kevork Exp $
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
`include "dut_env.sv"
  
  dut_env env;                     // DUT Environment

  initial begin
    env = new(ifcmas,ifcmon);                   // Create the environment
    env.build();                   // Build the environment 
    env.gen2mas.tee_mode(1);       // Enable Tee mode for thread below
    env.run();                     // Run all steps
  end 

  // Tee all elements from the generator, and print them
  initial fork
    forever begin
      apb_trans tr;
      env.gen2mas.tee(tr);
      tr.display("To Mst ==> ");
    end
  join_none

  
endprogram

