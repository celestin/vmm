program cntrlr_tb;
   `include "vmm.sv"
   `include "cntrlr_env.sv"
   `include "test.sv"

   //Environment
   cntrlr_env env;
  
   //Ports for connection with DUT
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

   // Lab 3 - Call vmm_opts::set_object() to connect the virtual ports
   vmm_opts::set_object("env:CPUDrv:cpu_port",cpu_port, null);
   vmm_opts::set_object("env:SRAM_0:sram_port",sram_port[0], null);
   vmm_opts::set_object("env:SRAM_1:sram_port",sram_port[1], null);
   vmm_opts::set_object("env:SRAM_2:sram_port",sram_port[2], null);
   vmm_opts::set_object("env:SRAM_3:sram_port",sram_port[3], null);

   vmm_simulation::list();
   vmm_simulation::run_tests();
end

endprogram
