//this is a write read test with number of scenarios to 50 

`include "cpu_write_read_scenario.sv"

class test_write_read extends vmm_test;
   `vmm_typename(test_write_read)

   function new(string name);
      super.new(name, "Test with WRITE follow by READ to the same address");
   endfunction

   virtual function void configure_test_ph();
      vmm_opts::set_int("%*:num_scenarios", 50);
      cpu_rand_scenario::override_with_new("@%*:CPUGen:rand_scn", cpu_write_read_scenario::this_type(), log, `__FILE__, `__LINE__);
   endfunction

endclass

test_write_read t_write_read = new("test_write_read");
