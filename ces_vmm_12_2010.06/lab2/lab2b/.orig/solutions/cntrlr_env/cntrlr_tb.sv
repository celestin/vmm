program cntrlr_tb;
   `include "vmm.sv"
   `include "cpuport.sv"
   `include "sramport.sv"
   `include "cntrlr_env.sv"
  
   // Lab 2b - Include the test class
   `include "test.sv"

   cntrlr_env env;
   cpuport    cpu_port;
   sramport   sram_port[];

initial begin
   env = new("env");
   cpu_port = new("cpu_port",test_top.cpuif);

   sram_port = new[4];
   sram_port[0] = new("sram_port", test_top.sramif0);
   sram_port[1] = new("sram_port", test_top.sramif1);
   sram_port[2] = new("sram_port", test_top.sramif2);
   sram_port[3] = new("sram_port", test_top.sramif3);

   // Lab 2b - List and Run the tests using vmm_simulation
   vmm_simulation::list();
   vmm_simulation::run_tests();
end

endprogram
