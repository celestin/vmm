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
// Filename    : $Id: apb_monitor.sv,v 1.12 2006/06/01 03:57:36 alexw Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: alexw $
//
// Author      : Angshu Saha, Alex Wakefield, Chris Spear
//
// Description : AMBA Peripheral Bus Monitor Transactor
//
//   This BFM constantly monitors the APB bus for transactions.
//   When a valid transaction is seen, a callback occurs.
//   Note the monitor calls the scoreboard directly
//
//    +--------------------+
//    |     APB-Monitor    |--------> Scoreboard
//    +--------------------+
//           |||||||
//           |||||||
//           APB Bus
//
//-----------------------------------------------------------------------------

`define APB_MONITOR_IF	apb_monitor_mp.monitor_cb
   
//-----------------------------------------------------------------------------
// APB Monitor Transactor Class
//-----------------------------------------------------------------------------
  
class apb_monitor extends vmm_xactor;
  
  // Factory Object for creating apb_trans
  apb_trans randomized_obj;

  // Scoreboard
  dut_scb scb;

  // APB Interface (Monitor side)
  virtual apb_if.Monitor apb_monitor_mp;

  extern function new(string instance,
                      int stream_id = -1,
                      virtual apb_if.Monitor apb_monitor_mp,
                      dut_scb scb);

  extern virtual task main() ;

  extern virtual task sample_apb(ref apb_trans tr);
    
endclass: apb_monitor

//-----------------------------------------------------------------------------
// APB Monitor Callback Class
//-----------------------------------------------------------------------------

typedef class apb_monitor;
  
virtual class apb_monitor_callbacks extends vmm_xactor_callbacks;

   // Callbacks before a transaction is started
   virtual task monitor_pre_rx(apb_monitor    xactor,
                               ref apb_trans trans);
   endtask

   // Callback after a transaction is completed
   virtual task monitor_post_rx(apb_monitor xactor,
                                apb_trans  trans);
   endtask

endclass: apb_monitor_callbacks
    
//-----------------------------------------------------------------------------
// new() - Constructor
//-----------------------------------------------------------------------------
  
function apb_monitor::new(string instance,
                          int stream_id,
                          virtual apb_if.Monitor apb_monitor_mp,
                          dut_scb scb);

  super.new("APB TRANS monitor", instance, stream_id) ;

  this.scb       = scb;

  // Create the default factory object
  randomized_obj = new();
    
  // Save the inteface into a local data member
  this.apb_monitor_mp = apb_monitor_mp;

endfunction: new

//-----------------------------------------------------------------------------
// main() - Monitor the APB bus, and invoke callbacks
//-----------------------------------------------------------------------------
    
task apb_monitor::main();

  apb_trans tr;
    
  // Call super.main to perform any base-class actions
  super.main();

  // Main Monitor Loop
  forever begin

    // Lab5 - Create a new apb_trans using the factory method
    // Lab5 - $cast(tr, randomized_obj.copy());
    $cast(tr, randomized_obj.copy());                                    //LAB5

    // Pre-Rx Callback
    `vmm_callback(apb_monitor_callbacks ,monitor_pre_rx(this, tr));

    // Sample the bus using the apb_sample() task
    sample_apb(tr);

    // Lab5 - Add a Post-Rx Callback. Typically for Coverage or Scoreboard
    // Lab5 - `vmm_callback, apb_monitor_callbacks, monitor_post_rx(this, tr)
    `vmm_callback(apb_monitor_callbacks, monitor_post_rx(this, tr));     //LAB5

    // Print the transaction in debug mode    
    `vmm_debug(log, tr.psdisplay("Monitor ==>"));

  end

endtask: main

//-----------------------------------------------------------------------------
// sample_apb() - Monitor and Sample the APB bus when a valid transaction occurs
//-----------------------------------------------------------------------------

task apb_monitor::sample_apb(ref apb_trans tr);

  bit Sel;
  bit Rd_nWr;
    
  // Wait for the device to be selected
  Sel = `APB_MONITOR_IF.PSel;
  if(Sel === 0) 
     @(posedge `APB_MONITOR_IF.PSel);

  // Wait for latch enable
  @(posedge `APB_MONITOR_IF.PEnable);

  // Read/Write cycle decision
  Rd_nWr = !`APB_MONITOR_IF.PWrite;

  // Read cycle - Store current transaction parameters 
  if(Rd_nWr == 1) begin
    tr.dir  = apb_trans::READ;
    tr.data = `APB_MONITOR_IF.PRData;
    tr.addr = `APB_MONITOR_IF.PAddr;
  end
  
  // Write Cycle - Store current transaction parameters
  if(Rd_nWr == 0) begin
    tr.dir  = apb_trans::WRITE;
    tr.data = `APB_MONITOR_IF.PWData;
    tr.addr = `APB_MONITOR_IF.PAddr;
  end
    
endtask: sample_apb
