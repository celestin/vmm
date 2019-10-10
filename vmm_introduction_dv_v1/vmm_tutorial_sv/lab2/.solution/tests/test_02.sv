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
// Filename    : $Id: test_02.sv,v 1.5 2006/06/05 14:56:40 kevork Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: kevork $
//
// Description : Simple Test for APB_Trans class
//
// Testbench code only, no DUT or Virtual Interfaces
//
//-----------------------------------------------------------------------------

program test(apb_if.Master ifcmas, apb_if.Monitor ifcmon);

`include "vmm.sv"
`include "apb_trans.sv"

  apb_trans t1, t2;         // Trans1 and Trans2 object handles
  string diff = "";         // Diff string for compare task

  initial begin
    // Crate a T1 transaction
    t1 = new();

    // Randomize T1, print T1
    t1.randomize();
    $display("T1 - Random Transaction");
    t1.display("T1 ==> ");
    
    // Copy T1 into T2, increment the data_id, print T2
    $cast(t2, t1.copy());
    t2.data_id = t1.data_id + 1;
    $display("T2 - Copy of Transaction T1");
    t2.display("T2 ==> ");

    $display("Compare T1 and T2 - should pass");
    // Compare T1 and T2, print messages
    if (t1.compare(t2, diff)) 
      $display("t1 and t2 compare OK, dif string is '%s'", diff);
    else
      $display("***t1 and t2 compare failed, dif string is '%s' ***", diff);
  end
endprogram







