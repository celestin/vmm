//Coverage model

class cntrlr_cov extends vmm_object;
   `vmm_typename(cntrlr_cov)
   cpu_trans  cpu_tr;
   sram_trans sram_tr;
   
   // Lab 4 - Create a coverage model with coverpoints set on some basic transaction fields.
   // ToDo


   function new(string name = "", vmm_object parent = null);
      super.new(parent, name);
      // Lab 4 - construct the covergroups
      // ToDo

   endfunction

   virtual function void sample_SRAM(sram_trans tr);
      this.sram_tr = tr;

      // Lab 4 - sample the covergroup CG_SRAM
      // ToDo

   endfunction

   virtual function void sample_CPU(cpu_trans tr);
      this.cpu_tr = tr;

      // Lab 4 - sample the covergroup CG_CPU
      // ToDo

   endfunction

endclass
