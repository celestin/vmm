program memsys_tb;
  `include "vmm.sv"
  `include "memsys_env.sv"
  `include "test1.sv"
  `include "test2.sv"
  `include "test_write.sv"

memsys_env                      env;
cpuport                         cpu_port0;
cpuport                         cpu_port1;

initial begin
   env = new("env");
   cpu_port0 = new("cpuport0",test_top.port0);
   cpu_port1 = new("cpuport1",test_top.port1);
   vmm_opts::set_object("CPU0:Drv:cpu_port",cpu_port0, env);
   vmm_opts::set_object("CPU1:Drv:cpu_port",cpu_port1, env);

   vmm_simulation::list();
   vmm_simulation::run_tests();
end


endprogram
