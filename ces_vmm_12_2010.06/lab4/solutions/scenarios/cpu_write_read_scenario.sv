class cpu_write_read_scenario extends cpu_rand_scenario;
   `vmm_typename(cpu_write_read_scenario)

   // Lab 4 - Declare instances of write and read scenarios
   cpu_write_scenario  write_scn;
   cpu_read_scenario   read_scn;

   // Lab 4 - Add the new members into the pre-defined base methods using 
   //         shorthand macros
   `vmm_scenario_new(cpu_write_read_scenario)

   `vmm_scenario_member_begin(cpu_write_read_scenario)
      `vmm_scenario_member_vmm_scenario(write_scn, DO_ALL)
      `vmm_scenario_member_vmm_scenario(read_scn, DO_ALL)
   `vmm_scenario_member_end(cpu_write_read_scenario)

   virtual task execute(ref int n);
      write_scn = cpu_write_scenario::create_instance(this, "write_scn", `__FILE__, `__LINE__);
      read_scn  = cpu_read_scenario::create_instance(this, "read_scn", `__FILE__, `__LINE__);
      write_scn.set_parent_scenario(this);
      read_scn.set_parent_scenario(this);

      // Lab 4 - randomize the write scenario
      if (!write_scn.randomize())
         `vmm_fatal(log, "cpu_write_read_scenario failed the write randomization");

      // Lab 4 - call the execute task to execute write
      write_scn.execute(n);

      // Lab 4 - randomize the read scenario
      read_scn.randomize() with { addr == write_scn.addr; };

      // Lab 4 - call the execute taks to execute read
      read_scn.execute(n);
  endtask

  `vmm_class_factory(cpu_write_read_scenario)
endclass
