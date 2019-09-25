class test extends vmm_test;

   function new(string name);
      super.new(name);
   endfunction

   virtual function void configure_test_ph();
      // Lab 3 - Set the stop after n scenarios attribute through vmm_opts
      //         to restrict the scenario count
      vmm_opts::set_int("env:num_scenarios", 50);
   endfunction

endclass

test t_random = new("test");
