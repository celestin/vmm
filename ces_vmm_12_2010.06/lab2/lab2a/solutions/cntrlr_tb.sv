program cntrlr_tb;
   `include "vmm.sv"
   `include "cpuport.sv"

   // Lab 2a - Include the transaction class and driver class
   `include "cntrlr_env.sv"

   cntrlr_env env;

   //Ports for connection with DUT
   cpuport                cpu_port;

initial begin
   cpu_port = new("cpu_port", test_top.cpuif);

   // Lab 2a - Construct the env object
   env = new("env");

   // Lab 2a - Call reset() to drive the DUT to reset.
   env.reset();

   // Lab 2a - Call the env.build() to build the transactor
   env.build();

   // Lab 2a - Call the env.run() to start the transactor
   env.run();
end

endprogram
