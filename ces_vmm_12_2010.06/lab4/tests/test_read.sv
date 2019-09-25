//this is a simple random test which sets number of scenarios to 50 
// through vmm_opts
// Lab 4 - Include the READ scenario class
// ToDo


class test_read extends vmm_test;
   `vmm_typename(test_read)

   function new(string name);
      super.new(name);
   endfunction

   virtual function void configure_test_ph();
      // Set the stop after n scenarios attribute through vmm_opts
      // to restrict the scenario count
      vmm_opts::set_int("%*:num_scenarios", 50);

      // Lab 4 - Override the default scenario with the READ sceanrio
      // ToDo


   endfunction

endclass
test_read t_read = new("test_read");
