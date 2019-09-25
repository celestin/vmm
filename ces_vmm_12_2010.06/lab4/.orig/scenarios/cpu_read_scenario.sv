class cpu_read_scenario extends cpu_rand_scenario;
   `vmm_typename(cpu_read_scenario)

   `vmm_scenario_new(cpu_read_scenario)

   `vmm_scenario_member_begin(cpu_read_scenario)
   `vmm_scenario_member_end(cpu_read_scenario)

   // Override the execute task to generate READ transactions
   virtual task execute(ref int n);
      cpu_trans tr;
      vmm_channel chan = get_channel("cpu_chan");
      $cast(tr, blueprint.copy());
      tr.stream_id = this.stream_id;
      tr.scenario_id = this.scenario_id;
      tr.data_id = 0;

      //Lab 4 - Randomize transaction to generate READ transactions
      // ToDo 


      chan.put(tr);
      n++;
   endtask

   `vmm_class_factory(cpu_read_scenario)
endclass
