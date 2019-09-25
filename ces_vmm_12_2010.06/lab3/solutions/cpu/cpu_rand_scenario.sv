class cpu_rand_scenario extends vmm_ms_scenario;
   `vmm_typename(cpu_rand_scenario)
   // Lab 3 - Declare an blueprint instance of cpu_trans transaction class
   cpu_trans       blueprint;

   rand bit [7:0] d;
   rand bit [9:0] addr;

   `vmm_scenario_new(cpu_rand_scenario)

   `vmm_scenario_member_begin(cpu_rand_scenario)
      `vmm_scenario_member_vmm_data(blueprint, DO_ALL, DO_REFCOPY) 
      `vmm_scenario_member_scalar(d, DO_ALL)
      `vmm_scenario_member_scalar(addr, DO_ALL)
   `vmm_scenario_member_end(cpu_rand_scenario)

   function new();
      // Lab 3 - Construct the blueprint instance within the new()
      blueprint = new();
   endfunction

   virtual task execute(ref int n);
      // Lab 3 - Overload the execute() task to generate random transactions
      cpu_trans tr;
      vmm_channel chan = get_channel("cpu_chan");
      $cast(tr, blueprint.copy());
      tr.stream_id = this.stream_id;
      tr.scenario_id = this.scenario_id;
      tr.data_id = 0;
      if (!tr.randomize())
         `vmm_fatal(log, "Rand Scenario randomization Failed!");;
      chan.put(tr);
      n++;
   endtask

   `vmm_class_factory(cpu_rand_scenario)
endclass
