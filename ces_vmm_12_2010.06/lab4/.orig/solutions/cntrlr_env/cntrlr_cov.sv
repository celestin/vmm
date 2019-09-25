//Coverage model

class cntrlr_cov extends vmm_object;
   `vmm_typename(cntrlr_cov)
   cpu_trans  cpu_tr;
   sram_trans sram_tr;
   
   // Lab 4 - Create a coverage model with coverpoints set on some basic transaction fields.
   covergroup CG_CPU;
      cp_kind: coverpoint cpu_tr.kind;
      cp_dly : coverpoint cpu_tr.trans_delay {
                  bins ZERO     = {0};
                  bins NON_ZERO = default;
               }
      cp_addr: coverpoint cpu_tr.address;
      cc_trans: cross cp_kind, cp_dly;
   endgroup

   covergroup CG_SRAM;
      option.per_instance = 1;
      cp_kind: coverpoint sram_tr.kind;
   endgroup

   function new(string name = "", vmm_object parent = null);
      super.new(parent, name);

      // Lab 4 - construct the covergroups
      CG_CPU = new;
      CG_SRAM = new;
   endfunction

   virtual function void sample_SRAM(sram_trans tr);
      this.sram_tr = tr;

      // Lab 4 - sample the covergroup CG_SRAM
      CG_SRAM.sample();
   endfunction

   virtual function void sample_CPU(cpu_trans tr);
      this.cpu_tr = tr;

      // Lab 4 - sample the covergroup CG_CPU
      CG_CPU.sample();
   endfunction

endclass


