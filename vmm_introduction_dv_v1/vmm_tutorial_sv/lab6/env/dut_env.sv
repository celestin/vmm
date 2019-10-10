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
// Filename    : $Id: dut_env.sv,v 1.26 2006/06/05 14:56:40 kevork Exp $
//
// Created by  : Synopsys Inc. 09/01/2004
//               $Author: kevork $
//
// Authors     : Angshuman Saha, Alex Wakefield, Chris Spear
//
//
// Description : APB Testbench vmm_environment class
//
// This class instantiates all the permanent testbench top-level components
//
// After all the labs have been completed, this will include:
//   * APB Atomic Generator
//   * APB Master
//   * APB Monitor
//   * Scoreboard
//
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// dut_env class
//-----------------------------------------------------------------------------

class dut_env extends vmm_env;

  // APB Master/Monitor Virtual Interface
  virtual apb_if.Master  ifcmas;
  virtual apb_if.Monitor ifcmon;

  // Lab1 - Add a VMM logger for messages  (vmm log log)
  vmm_log log;                                                           //LAB1

  // Lab1 - Add an apb_cfg handle here with name "cfg"
  apb_cfg cfg;                                                           //LAB1
                                                                         //LAB1
  // Lab3 - Add a channel here for the output generator called gen2mas
  apb_trans_channel gen2mas;                                             //LAB3
                                                                         //LAB3
  // Lab3 - Add a handle here for apb_trans_atomic_gen called gen
  apb_trans_atomic_gen gen;                                              //LAB3
                                                                         //LAB3
  // Lab4 - Add a handle here for apb_master called mst
  apb_master            mst;                                             //LAB4
                                                                         //LAB4
  // Lab5 - Add a handle here for apb_monitor called mon
  apb_monitor           mon;                                             //LAB5
                                                                         //LAB5
  // Lab5 - Add a handle here for dut_scb called scb
  dut_scb                scb;                                            //LAB5
                                                                         //LAB5
  // Constructor
  extern function new(virtual apb_if.Master ifcmas,virtual apb_if.Monitor ifcmon);

  // VMM Environment Steps
  extern virtual function void gen_cfg();
  extern virtual function void build();
  extern virtual task reset_dut();
  extern virtual task cfg_dut();
  extern virtual task start();
  extern virtual task wait_for_end();
  extern virtual task stop();
  extern virtual task cleanup();
  extern virtual task report();

endclass: dut_env

//-----------------------------------------------------------------------------
// new() - constructor, pass in any virtual ports needed to connect to DUT
//-----------------------------------------------------------------------------

  function dut_env::new(virtual apb_if.Master ifcmas, virtual apb_if.Monitor ifcmon);

    // Pass in the name of the environment to the VMM-Env logger class
    super.new("DUT_ENV");

    // Save a copy of the virtual interfaces
    this.ifcmas = ifcmas;
    this.ifcmon = ifcmon;

    // Lab1 - Construct/new() the log using new("dut", "env")
    log = new("dut", "env");                                             //LAB1

    // Lab1 -  Construct/new() the cfg object here
    this.cfg = new();                                                    //LAB1

endfunction

//-----------------------------------------------------------------------------
// gen_cfg() - Generate a randomized testbench configuration
//-----------------------------------------------------------------------------

function void dut_env::gen_cfg();

  super.gen_cfg();

  // Lab1 - Randomize the cfg object here, print a fatal message if the
  // Lab1 - randomization fails (returns 0)
  if (cfg.randomize() == 0)                                              //LAB1
    `vmm_fatal(log, "Failed to randomize testbench configuration");      //LAB1
                                                                         //LAB1
  // Lab1 - Add a `vmm_note print statement here to display the cfg.trans_cnt
  `vmm_note(log, $psprintf("cfg.trans_cnt = %0d", cfg.trans_cnt));       //LAB1
                                                                         //LAB1
endfunction

//-----------------------------------------------------------------------------
// build() - Build the testbench, xactors, scoreboard, callbacks
//-----------------------------------------------------------------------------

function void dut_env::build();

  super.build();

  // Lab3 - Create a channel to connect the atomic generator to the master
  // Lab3 - new(), gen2mas, "APB Trans Channel", "gen2mas"
  gen2mas = new ("APB Trans Channel", "gen2mas");                        //LAB3
                                                                         //LAB5
  // Lab3 - Create the gen handle by calling new here
  // Lab3 - "APB Atomic Gen", instance = 1, channel = gen2mas
  gen = new ("APB Atomic Gen", 1, gen2mas);                              //LAB3
                                                                         //LAB3
  // Lab4 - Create the mst object by calling new() with arguments:
  // Lab4 - "APB trans master", 1, ifcmas, gen2mas
  mst = new ("APB trans master", 1, ifcmas, gen2mas );                      //LAB4
                                                                         //LAB4
  // Lab5 - Create the scb transactor instance
  // Lab5 - Pass in the transaction count from the configuation object
  scb = new(cfg.trans_cnt);                                              //LAB5
                                                                         //LAB5
  // Lab5 - Create the mon object by calling new with arguments:
  // Lab5 - "APB trans monitor", 1, ifcmon, scb
  mon = new ("APB trans monitor", 1, ifcmon, scb);				 //LAB5
                                                                         //LAB5
  // Lab6 - Integrate the scoreboard using callbacks
  // Lab6 - Enclose the following 2 lines in a begin/end block
  // Lab6 - Create a new apb_master_scb_callbacks object apb_mst_scb_cb
  // Lab6 - Append this using mst.append_callback(apb_mst_scb_cb)





  // Lab6 - Enclose the following 2 lines in a begin/end block
  // Lab6 - Create a new apb_monitor_scb_callbacks object apb_mon_scb_cb
  // Lab6 - Append this using mon.append_callback(apb_mon_scb_cb)






  // Lab3 - Configure the generator to stop after cfg.trans_cnt instances
  // Lab3 - use the gen.stop_after_n_insts handle
  gen.stop_after_n_insts = cfg.trans_cnt;                                //LAB3
endfunction: build

//-----------------------------------------------------------------------------
// reset_dut() - Reset the DUT
//-----------------------------------------------------------------------------

task dut_env::reset_dut();

  super.reset_dut();

  // Lab4 - Reset the APB master by calling mst.reset()
  mst.reset();                                                           //LAB4
                                                                         //LAB4
endtask:reset_dut

//-----------------------------------------------------------------------------
// cfg_dut() - Configure the DUT
//-----------------------------------------------------------------------------

task dut_env::cfg_dut();

  super.cfg_dut();

endtask: cfg_dut

//-----------------------------------------------------------------------------
// start() - Start each of the xactors
//-----------------------------------------------------------------------------

task dut_env::start();

  super.start();

  // Lab3 - Add call to start_xactor for gen
  gen.start_xactor();                                                    //LAB3
  // Lab4 - Add call to start_xactor for mst
  mst.start_xactor();                                                    //LAB4
  // Lab5 - Add call to start_xactor for mon
  mon.start_xactor();                                                    //LAB5
  // Lab6 - Add call to start_xactor for scb


endtask: start

//-----------------------------------------------------------------------------
// wait_for_end() - Wait until the test completes
//-----------------------------------------------------------------------------

task dut_env::wait_for_end();

  super.wait_for_end();

  // Lab3 - Wait for notification from gen and scoreboard
  // Lab3 - by calling gen.notify.wait_for(apb_trans_atomic_gen::DONE)
  // Lab6 - Wait for two notifiers in a fork-join_any block.
  // Lab6 - First, the existing gen.notify then scb.notify.wait_for(scb.DONE)
  // Lab6 - Note vmm builtin notify is enum int, so use "class::enum"
  // Lab6 - User notify is int so use "handle.datamember"

    gen.notify.wait_for(apb_trans_atomic_gen::DONE);                     //LAB3



endtask: wait_for_end

//-----------------------------------------------------------------------------
// stop() - Stop each of the xactors
//-----------------------------------------------------------------------------

task dut_env::stop();

  super.stop();

  // Lab3 - Add call to stop_xactor for gen
  gen.stop_xactor();                                                     //LAB3
  // Lab4 - Add call to stop_xactor for mst
  mst.stop_xactor();                                                     //LAB4
  // Lab5 - Add call to stop_xactor for mon
  mon.stop_xactor();                                                     //LAB5
                                                                         //LAB5
endtask: stop

//-----------------------------------------------------------------------------
// cleanup() - Cleanup the testbench, report any scoreboard errors etc.
//-----------------------------------------------------------------------------

task dut_env::cleanup();

  super.cleanup();

  // Lab6 - Add a call to the scb.cleanup() task here


endtask

//-----------------------------------------------------------------------------
// report() - Report Statistics from the testbench
//-----------------------------------------------------------------------------

task dut_env::report();

  super.report();

  // Lab6 - Add a call to the scb.report() task here


endtask

