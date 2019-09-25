class sramport extends vmm_object;
   virtual sram_if.memprt sigs;

   function new(string name,virtual sram_if.memprt sigs);
      super.new(null, name);
      this.sigs = sigs;
   endfunction
endclass
