class cpu_rand_scenario extends vmm_ms_scenario;
   `vmm_typename(cpu_rand_scenario)

   // Lab 3 - Declare an blueprint instance of cpu_trans transaction class
   // ToDo


   rand bit[7:0] d;
   rand bit[9:0] addr;

   `vmm_scenario_new(cpu_rand_scenario)

   `vmm_scenario_member_begin(cpu_rand_scenario)
      `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
      `vmm_scenario_member_scalar(d, DO_ALL)
      `vmm_scenario_member_scalar(addr, DO_ALL)
   `vmm_scenario_member_end(cpu_rand_scenario)

   function new();
      // Lab 3 - Construct the blueprint instance within the new()
      // ToDo

   endfunction

   virtual task execute(ref int n);
      // Lab 3 - Override the execute() task to generate random transactions
      // ToDo

   endtask

   `vmm_class_factory(cpu_rand_scenario)
endclass
