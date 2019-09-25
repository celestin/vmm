//this is a simple random test which sets number of scenarios to 50 
// through vmm_opts
// Lab 4 - Include the write scenario class
// ToDo


class test_write extends vmm_test;
   `vmm_typename(test_write)

   function new(string name);
      super.new(name);
   endfunction

   virtual function void configure_test_ph();
      // Set the stop after n scenarios attribute through vmm_opts
      // to restrict the scenario count
      vmm_opts::set_int("%*:num_scenarios", 50);

      // Lab 4 - Override the default scenario with WRITE scenario
      // ToDo

   endfunction

endclass
test_write t_write = new("test_write");
