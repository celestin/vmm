class test extends vmm_test;

   function new(string name, string doc);
      super.new(name, doc);
   endfunction

   virtual function void start_of_sim_ph();
      // lab 2b - Add a note message to signal the start of simulation
      // ToDo

   endfunction

endclass
test t_obj = new("test", "Simple Test");
