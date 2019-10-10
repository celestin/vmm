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
// Filename    : $Id: cov_callbacks.sv,v 1.7 2005/09/23 23:54:24 alexw Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: alexw $
//               Angshu Saha
//               Benjamin Chin
//
// Description : Coverage Callbacks
//
//               This class is DUT specific, and collects coverage 
//
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// coverage  APB Master Callback Class
//-----------------------------------------------------------------------------

typedef class apb_trans;
    
class apb_master_cov_callbacks extends apb_master_callbacks;
  local apb_trans tr ;
    
  covergroup apb_trans_cov;

    addr: coverpoint tr.addr {
      bins zero = {0};
      bins onek = {1024};
      bins others = default;
    }

    // Lab7 - add coverpoints for data == 0, 1k, others






   endgroup
    
  // Callbacks before a transaction is started
  virtual task master_pre_tx(apb_master    xactor,
                             ref apb_trans trans,
                             ref bit        drop);
   // Empty
  endtask

  // Callback after a transaction is completed
  virtual task master_post_tx(apb_master xactor,
                              apb_trans  trans);

    tr = trans ;                  // Save a handle to the transaction
    apb_trans_cov.sample();       // Sample Coverage

  endtask

  function new();
    apb_trans_cov = new();
  endfunction: new    

endclass: apb_master_cov_callbacks
