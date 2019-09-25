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





`include "cntrlr_sb.sv"
class cntrlr_sb_top extends vmm_xactor;

   `vmm_tlm_analysis_export(_cpu_trans_started)
   `vmm_tlm_analysis_export(_cpu_trans_ended)
   `vmm_tlm_analysis_export(_sram)
   
    vmm_tlm_analysis_export_cpu_trans_started  #(cntrlr_sb_top, cpu_trans) cpu_start_export = new(this, "CpuAnPort", 10, 0);
    vmm_tlm_analysis_export_cpu_trans_ended  #(cntrlr_sb_top, cpu_trans) cpu_end_export = new(this, "CpuAnPort", 10, 0);
    vmm_tlm_analysis_export_sram #(cntrlr_sb_top, sram_trans) sram_export = new(this, "SramAnPort", 10, 0);

    cpu2sram_sb cpu2sram;
    sram2cpu_sb  sram2cpu;
   
    cpu_config cpu_cfg;
    sram_config sram_cfg;
    int  addr_wdth;

    int is_set; 

   function new(string inst="",vmm_object parent = null);
      super.new(get_typename(),inst,0,parent);
   endfunction

   function void build_ph();
      $cast(sram_cfg, vmm_opts::get_object_obj(is_set,this,"sram_cfg"));
      if(sram_cfg == null) `vmm_fatal(log,"Null Configuration Obtained for SRAM in SB");
     addr_wdth = sram_cfg.get_addr_width();
     cpu2sram = new("CPU->SRAM", sram_cfg.num_sram_devices, sram_cfg.get_addr_width());
     sram2cpu = new("SRAM->CPU", sram_cfg.num_sram_devices, sram_cfg.get_addr_width());
   endfunction

   function int get_stream_id(bit [31:0] addr);
      if (sram_cfg.num_sram_devices == 1) return 0;
      if (sram_cfg.num_sram_devices == 2) return addr[addr_wdth];
      if (sram_cfg.num_sram_devices == 4) 
      begin
        if ( sram_cfg.get_addr_width() ==8) return addr[9:8];
        if ( sram_cfg.get_addr_width() ==9) return addr[10:9];
        if ( sram_cfg.get_addr_width() ==10) return addr[11:10];
      end
   endfunction

   function void write_cpu_trans_started(int id=-1, cpu_trans tr);
     `vmm_trace(log, tr.psdisplay("@CPU Trans Started "));
      cpu2sram.inp_insert(tr,.exp_stream_id(get_stream_id(tr.address)));
   endfunction

   function void write_cpu_trans_ended(int id=-1, cpu_trans tr);
     `vmm_trace(log, tr.psdisplay("@CPU Trans Completed "));
      sram2cpu.expect_in_order(tr, .inp_stream_id(get_stream_id(tr.address)));
   endfunction

   function void write_sram(int id=-1, sram_trans tr);
     `vmm_trace(log, tr.psdisplay("@SRAM Trans "));
      sram2cpu.inp_insert(tr, .inp_stream_id(id));
      cpu2sram.expect_out_of_order(tr, .exp_stream_id(id));
   endfunction

endclass

