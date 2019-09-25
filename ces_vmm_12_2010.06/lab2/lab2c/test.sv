class test extends vmm_test;

   // Lab 2c - Include the newly created callback class files
   // ToDo


   // Lab 2c - Declare a CPU callback object
   // ToDo


   // Lab 2c - Declare a SRAM callback object
   // ToDo


   function new(string name);
      super.new(name);
   endfunction

   function void build_ph();
      super.build_ph();
      // Lab 2c - Construct the callback objects
      // ToDo

   endfunction

   function void connect_ph();
      super.connect_ph();
      // Lab 2c - Append the corresponding callback elements with the transactors.
      // ToDo 

   endfunction

   function void start_of_sim_ph();
      super.start_of_sim_ph();
      `vmm_note(this.log, "Entering start_of_sim_ph()");
   endfunction

endclass
test t_obj = new("test");
