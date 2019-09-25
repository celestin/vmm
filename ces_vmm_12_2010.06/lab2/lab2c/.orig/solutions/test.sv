class test extends vmm_test;

   // Lab 2c - Include the newly created callback class files
   `include "cpu_callbacks.sv"
   `include "sram_callbacks.sv"

   // Lab 2c - Declare a CPU callback object
   cpu_callbacks cpu_cb;

   // Lab 2c - Declare a SRAM callback object
   sram_callbacks sram_cb;

   function new(string name);
      super.new(name);
   endfunction

   function void build_ph();
      super.build_ph();
      // Lab 2c - Construct the callback objects
      cpu_cb = new();
      sram_cb = new();
   endfunction

   function void connect_ph();
      super.connect_ph();
      // Lab 2c - Append the corresponding callback elements with the transactors.
      env.drv.append_callback(cpu_cb);
      foreach (env.rams[i])
         env.rams[i].append_callback(sram_cb);
   endfunction

   function void start_of_sim_ph();
      super.start_of_sim_ph();
      `vmm_note(this.log, "Entering start_of_sim_ph()");
   endfunction

endclass
test t_obj = new("test");
