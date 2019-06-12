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





//Coverage model

class cntrlr_cov extends vmm_object;
   `vmm_typename(cntrlr_cov)
   cpu_trans  cpu_tr;
   sram_trans sram_tr;
   int sram_id;
   `vmm_tlm_analysis_export(_CPU)
   `vmm_tlm_analysis_export(_SRAM)
   
    vmm_tlm_analysis_export_CPU  #(cntrlr_cov, cpu_trans) cpu_export = new(this, "CpuAnPort", 10, 0);
    vmm_tlm_analysis_export_SRAM #(cntrlr_cov, sram_trans) sram_export = new(this, "SramAnPort", 10, 0);
   
   covergroup CG_CPU;
      cp_kind: coverpoint cpu_tr.kind;
      cp_dly : coverpoint cpu_tr.trans_delay {
                  bins ZERO     = {0};
                  bins NON_ZERO = {[1:5]};
               }
      cp_addr: coverpoint cpu_tr.address;
      cc_trans: cross cp_kind, cp_dly;
   endgroup

   covergroup CG_SRAM;
      cp_kind: coverpoint sram_tr.kind;
      cp_id  : coverpoint sram_id {
                  bins SRAM[] = {[0:3]};
               }
      cc_trans: cross cp_kind, cp_id;
   endgroup

   function new(string name = "", vmm_object parent = null);
      super.new(parent, name);
      CG_CPU = new;
      CG_SRAM = new;
   endfunction

   virtual function void write_SRAM(int id=-1, sram_trans tr);
     this.sram_id = id;
     this.sram_tr = tr;
     CG_SRAM.sample();
   endfunction

   virtual function void write_CPU(int id=-1, cpu_trans tr);
     this.cpu_tr = tr;
     CG_CPU.sample();
   endfunction

endclass


