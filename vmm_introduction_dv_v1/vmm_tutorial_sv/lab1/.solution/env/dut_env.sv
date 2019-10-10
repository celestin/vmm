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


endfunction: build

//-----------------------------------------------------------------------------
// reset_dut() - Reset the DUT
//-----------------------------------------------------------------------------

task dut_env::reset_dut();

  super.reset_dut();

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


endtask: start

//-----------------------------------------------------------------------------
// wait_for_end() - Wait until the test completes
//-----------------------------------------------------------------------------

task dut_env::wait_for_end();

  super.wait_for_end();

endtask: wait_for_end

//-----------------------------------------------------------------------------
// stop() - Stop each of the xactors
//-----------------------------------------------------------------------------

task dut_env::stop();

  super.stop();

endtask: stop

//-----------------------------------------------------------------------------
// cleanup() - Cleanup the testbench, report any scoreboard errors etc.
//-----------------------------------------------------------------------------

task dut_env::cleanup();

  super.cleanup();

endtask

//-----------------------------------------------------------------------------
// report() - Report Statistics from the testbench
//-----------------------------------------------------------------------------

task dut_env::report();

  super.report();

endtask

