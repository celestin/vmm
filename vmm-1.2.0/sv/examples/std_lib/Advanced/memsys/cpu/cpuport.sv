class cpuport extends vmm_object;
   virtual cpu_if.drvprt iport;

   function new(string name,virtual cpu_if.drvprt iport);
     super.new(null, name);
     this.iport = iport;
   endfunction
endclass
