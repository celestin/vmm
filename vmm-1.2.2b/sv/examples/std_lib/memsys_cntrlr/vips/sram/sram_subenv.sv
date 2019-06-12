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

`include "sram_trans.sv"
`include "sram_config.sv"
`include "sramport.sv"
`include "sram_monport.sv"
`include "sram_model.sv"
`include "sram_monitor.sv"

class sram_subenv extends vmm_group;
 `vmm_typename(sram_subenv)
  typedef enum {ACTIVE, PASSIVE} subenv_type_e;

  subenv_type_e        subenv_type = ACTIVE;
  sram_config          cfg;
  // driver instance
  sram_model           rams[];

  sram_monitor         mon_rams[];

  extern function new(string inst, 
                      vmm_unit parent=null);
  extern virtual function void build_ph();
  extern virtual task          shutdown_ph();
int is_set;
endclass

/*******************************************************************************
  new() :  constructor
*******************************************************************************/
function sram_subenv::new(string inst, vmm_unit parent);
  super.new(get_typename(), inst, parent);
endfunction

/*******************************************************************************
  build_ph() :  build components
*******************************************************************************/
function void sram_subenv::build_ph();
   $cast(cfg, vmm_opts::get_object_obj(is_set,this,"sram_cfg"));
   if (cfg == null) `vmm_fatal(log, "Null Configuration Obtained for SRAM subenv");
   if (subenv_type == ACTIVE) begin
      this.rams = new [cfg.num_sram_devices];
      for (int i=0; i<cfg.num_sram_devices; i++) begin
        string str = $psprintf("%s_%0d", get_object_name(), i);
        this.rams[i] = new(str, this);
      end
   end
   else begin
      this.mon_rams = new [cfg.num_sram_devices];
      for (int i=0; i<cfg.num_sram_devices; i++) begin
        string str = $psprintf("%s_%0d", get_object_name(), i);
        this.mon_rams[i] = new(str, this);
      end
   end
endfunction

/*******************************************************************************
  shutdown_ph() :  stop components
*******************************************************************************/
task sram_subenv::shutdown_ph();
endtask


