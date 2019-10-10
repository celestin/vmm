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
// Filename    : $Id: scb_callbacks.sv,v 1.3 2006/05/10 19:01:34 alexw Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: alexw $
//               Angshu Saha
//
// Description : Scoreboard Integration/Callbacks
//
//               This class is DUT specific, and connects the scoreboard
//               to the Testbench.
//
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Scoreback Connection via APB Master Callback Class
//-----------------------------------------------------------------------------

typedef class apb_master;
typedef class dut_scb;
    
class apb_master_scb_callbacks extends apb_master_callbacks;

  dut_scb scb;
    
  // Constructor
  function new(dut_scb scb);
    this.scb = scb;
  endfunction: new
    
  // Callbacks before a transaction is started
  virtual task master_pre_tx(apb_master    xactor,
                             ref apb_trans trans,
                             ref bit        drop);
   // Empty
  endtask

  // Callback after a transaction is completed
  virtual task master_post_tx(apb_master xactor,
                              apb_trans  trans);
    // Lab6 - call the scoreboard task from_master() and pass trans
    scb.from_master(trans);                                               //LAB6
  endtask

endclass: apb_master_scb_callbacks


//-----------------------------------------------------------------------------
// APB Monitor Callback Class
//-----------------------------------------------------------------------------

typedef class apb_monitor;
  
class apb_monitor_scb_callbacks extends apb_monitor_callbacks;

  dut_scb scb;
    
   // Constructor
  function new(dut_scb scb);
    this.scb = scb;
  endfunction: new

  // Callbacks before a transaction is started
  virtual task monitor_pre_rx(apb_monitor    xactor,
                              ref apb_trans trans);
  endtask

  // Callback after a transaction is completed
  virtual task monitor_post_rx(apb_monitor xactor,
                               apb_trans  trans);
    // Lab6 - call the scoreboard task from_monitor() and pass trans
    scb.from_monitor(trans);                                              //LAB6
  endtask

endclass: apb_monitor_scb_callbacks
