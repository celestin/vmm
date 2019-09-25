class cpu_cov_callbacks extends cpu_driver_callbacks;

   // Lab 4 - Declare an instance of the coverage class
   // ToDo

  
   function new(cntrlr_cov cov);
      // Lab 4 - Assign the local coverage with the one received by the constructor
      // ToDo

   endfunction

   virtual task post_trans(cpu_driver drv, cpu_trans tr);
      // Lab 4 - call sample_CPU() method to sample the CPU transaction fields
      // ToDo

   endtask

endclass
