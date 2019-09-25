class test extends vmm_test;

   function new(string name);
      super.new(name);
   endfunction

   virtual function void start_of_sim_ph();
      // lab 2b - Add a note message to signal the start of simulation
      `vmm_note(this.log, "Entering start_of_sim_ph()");
   endfunction

endclass
test t_obj = new("test");
