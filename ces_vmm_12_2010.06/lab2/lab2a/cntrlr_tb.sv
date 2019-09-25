program automatic cntrlr_tb;
   `include "vmm.sv"
   `include "cpuport.sv"

   // Lab 2a - Include the env class
   // ToDo


   // Lab 2a - Declare an instance of the cntrlr_env, use env as instance name
   // ToDo


   //Ports for connection with DUT
   cpuport                cpu_port;

initial begin
   cpu_port = new("cpu_port",test_top.cpuif);

   // Lab 2a - Construct the env object
   // ToDo


   // Lab 2a - Call the env.build() to build the transactor
   // ToDo


   // Lab 2a - Call the env.reset() to drive the DUT to reset.
   // ToDo


   // Lab 2a - Call the env.run() to start the transactor
   // ToDo

end

endprogram
