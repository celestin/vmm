//////////////////////////////////////////////////////////////////////////////
//
//  DDDDD   OOO  UU UU LL    OOO   SSS
//  DD  DD OO OO UU UU LL   OO OO SS  S
//  DD  DD OO OO UU UU LL   OO OO  SS
//  DD  DD OO OO UU UU LL   OO OO   SS
//  DD  DD OO OO UU UU LL   OO OO S  SS
//  DDDDD   OOO   UUU  LLLL  OOO   SSS
//
//  Doulos
//
//  Filename: wb_spi_pkg
//  Date: 2 Nov 2009
//  Author: Doug Smith
//  Description:  Package containing all the testbench classes.
//
//////////////////////////////////////////////////////////////////////////////


package wb_spi_pkg;

  `include "vmm.sv"
  `include "wb_spi_defines.svh"

  // Transaction classes
  `include "wb_spi_trans.svh"
  `include "wb_spi_trans.sv"
  `include "mon_sb_trans.sv"

  // Interface wrapper
  `include "dut_if_wrapper.sv"

  // Scenarios
  `include "scenarios.sv"

  // SPI
  `include "spi_monitor.sv"

  // WB Subenv
  `include "wb_driver.sv"
  `include "wb_monitor.sv"
  `include "wb_subenv.sv"

  // Scoreboard
  `include "wb_spi_scoreboard.sv"

  // Environment
  `include "wb_spi_env.sv"

  // Test cases
  `include "wb_test1.sv"

endpackage : wb_spi_pkg
