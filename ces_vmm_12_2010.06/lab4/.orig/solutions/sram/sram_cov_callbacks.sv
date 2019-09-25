class sram_cov_callbacks extends sram_model_callbacks;

   // Lab 4 - Declare an instance of the coverage class
   cntrlr_cov cov;
  
   function new(cntrlr_cov cov);

     // Lab 4 - Assign the local coverage with the one received by the constructor
      this.cov = cov;
   endfunction
  
   virtual task post_trans(sram_model drv, sram_trans tr);

      // Lab 4 - call sample_SRAM() method to sample the SRAM transaction fields
      cov.sample_SRAM(tr);
   endtask
endclass
