//this is a simple random test which sets number of scenarios to 50 
// through vmm_opts
`include "cpu_write_scenario.sv"
class test_write extends vmm_test;
  `vmm_typename(test_write)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void configure_test_ph();
     // Set the stop after n scenarios attribute through vmm_opts
     // to restrict the scenario count
     vmm_opts::set_int("%*:num_scenarios", 50);

     // Lab 4 - Override the default scenario by calling the override_with_new() method.
     cpu_rand_scenario::override_with_new("@%*:CPUGen:rand_scn", cpu_write_scenario::this_type(), log, `__FILE__, `__LINE__);
  endfunction

endclass

test_write t_write = new("test_write");
