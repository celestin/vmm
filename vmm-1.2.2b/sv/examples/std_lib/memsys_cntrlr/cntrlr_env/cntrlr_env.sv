//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//





`include "cpu_subenv.sv"
`include "sram_subenv.sv"
`include "cntrlr_config.sv"
`include "cntrlr_cov.sv"
`include "cntrlr_sb_top.sv"

class cntrlr_env extends vmm_group;

  cpu_subenv                       cpu;

  vmm_consensus                    end_vote;

  sram_subenv                      mem;

  cntrlr_sb_top                    sbtop;

  cntrlr_cov                       cov;

  int                              timeout;

  //extern methods
  extern  function new(string name, vmm_unit parent=null);
  extern  virtual function void build_ph();
  extern virtual function void configure_ph();
  extern  virtual function void connect_ph();
  extern  virtual task reset_ph();
  extern  virtual task run_ph();
  extern  virtual task shutdown_ph();
  extern  virtual function void report_ph();


endclass

function cntrlr_env::new(string name, vmm_unit parent);
  super.new(get_typename(), name, parent);
endfunction


function void cntrlr_env::build_ph();
 
 `vmm_trace(log, "Building components...");

   //Building the components
   cpu = new("CPU", this);
   mem = new("SRAM", this);

   //Coverage model
   cov = new("cov", this);

   //Building Scoreboard component
   sbtop = new("SBTOP",this);

endfunction


function void cntrlr_env::configure_ph();
   timeout = vmm_opts::get_int("TIMEOUT", 10000000, "Simulation Timout Limit");
endfunction

function void cntrlr_env::connect_ph();
  //Scoreboard Connectivity through TLM analysys port/export
  cpu.drv.pre_analysis_port.tlm_bind(sbtop.cpu_start_export);
  cpu.drv.analysis_port.tlm_bind(sbtop.cpu_end_export);
  for (int i=0; i<cntrlr_cfg.sram_cfg.num_sram_devices; i++) begin
    mem.rams[i].analysis_port.tlm_bind(sbtop.sram_export);
  end

  //Coverage connectivity through TLM analysis port/export
  cpu.drv.analysis_port.tlm_bind(cov.cpu_export);
  for (int i=0; i<cntrlr_cfg.sram_cfg.num_sram_devices; i++) begin
    mem.rams[i].analysis_port.tlm_bind(cov.sram_export);
  end
  
endfunction

task cntrlr_env::reset_ph();
  `vmm_verbose(this.log,"Resetting DUT...");
  test_top.reset <= 1'b0;
  repeat(1) @(test_top.cpuif.cb)
  test_top.reset <= 1'b1;
  repeat(10) @(test_top.cpuif.cb)
  test_top.reset <= 1'b0;
  `vmm_verbose(this.log,"RESET DONE...");
endtask


task cntrlr_env::run_ph();
   fork begin
     #timeout; //Timeout
     `vmm_fatal(log, "Timeout Limit Reached!! Exiting Simulation...");
   end join_none
endtask

task cntrlr_env::shutdown_ph();
  sbtop.cpu2sram.notify.wait_for(vmm_sb_ds::EMPTY);
  sbtop.sram2cpu.notify.wait_for(vmm_sb_ds::EMPTY);
endtask

function void cntrlr_env::report_ph();
  sbtop.cpu2sram.report();
  sbtop.sram2cpu.report();
endfunction




