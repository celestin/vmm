class cpu_write_scenario extends cpu_rand_scenario;
   `vmm_typename(cpu_write_scenario)

   `vmm_scenario_new(cpu_write_scenario)

   `vmm_scenario_member_begin(cpu_write_scenario)
   `vmm_scenario_member_end(cpu_write_scenario)

   // Lab 4 - Override the execute task to generate WRITE transactions
   virtual task execute(ref int n);
      cpu_trans tr;
      vmm_channel chan = get_channel("cpu_chan");
      $cast(tr, blueprint.copy());
      tr.stream_id = this.stream_id;
      tr.scenario_id = this.scenario_id;
      tr.data_id = 0;

      // Lab 4 - Randomize the transaction to generate WRITE transactions
      if (!tr.randomize() with { kind == WRITE; address == addr; data == d; })
         `vmm_fatal(log, "Write Scenario randomization Failed!");
      chan.put(tr);
      n++;
   endtask

   `vmm_class_factory(cpu_write_scenario)
endclass
