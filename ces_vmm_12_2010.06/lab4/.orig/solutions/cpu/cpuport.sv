class cpuport extends vmm_object;
   virtual cpu_if.drvprt sigs;

   function new(string name,virtual cpu_if.drvprt sigs);
      super.new(null, name);
      this.sigs = sigs;
   endfunction
endclass
