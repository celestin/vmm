class cpu_cov_callbacks extends cpu_driver_callbacks;

   // Lab 4 - Declare an instance of the coverage class
   cntrlr_cov cov;
  
   function new(cntrlr_cov cov);
      // Lab 4 - Assign the local coverage with the one received by the constructor
      this.cov = cov;
   endfunction

   virtual task post_trans(cpu_driver drv, cpu_trans tr);
      // Lab 4 - call sample_CPU() method to sample the CPU transaction fields
      cov.sample_CPU(tr);
   endtask

endclass
