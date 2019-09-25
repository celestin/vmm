program automatic test;
`include "tb_env.sv"
// Lab 4 - Add include statement for test_scenario.sv
// ToDo
`include "test_scenario.sv"

class testcase_Packet extends Packet;
   constraint test_constraint {
      this.payload.size inside {[2:4]};
   }
   `vmm_data_member_begin(testcase_Packet)
   `vmm_data_member_end(testcase_Packet)
endclass

constraint test_cfg::testcase {
   run_for_n_packets == 2000;
}

// Lab 4 - Create a test for scenario generation of walking 0's and walking 1's
// ToDo
`vmm_test_begin(scenario, tb_env, "Walking 0's and Walking 1's")
   this.env.build();
   begin
      test_scenario scen = new();
      testcase_Packet pkt = new();
      this.env.blueprint.copy(pkt);
      scen.using = pkt;
      this.env.gen.scenario_set[0] = scen;
   end
   this.env.run();
`vmm_test_end(scenario)


`vmm_test_begin(all_ports, tb_env, "All Ports")
   this.env.cfg.num_of_iports = 16;
   this.env.cfg.num_of_oports = 16;
   this.env.cfg.num_of_iports.rand_mode(0);
   this.env.cfg.num_of_oports.rand_mode(0);
   this.env.build();
   begin
      testcase_Packet pkt = new();
      this.env.blueprint.copy(pkt);

      // Lab 4 - Update scenario generator's blueprint object via using
      // ToDo
      foreach (this.env.gen.scenario_set[i])
         this.env.gen.scenario_set[i].using = pkt;

   end
   this.env.run();
`vmm_test_end(all_ports)

class testcase_cfg extends test_cfg;
   constraint one_port {
      num_of_iports == 1;
      num_of_oports == 1;
   }
endclass

`vmm_test_begin(one_port, tb_env, "One Port")
   testcase_cfg cfg = new();
   this.env.cfg = cfg;
   this.env.build();
   begin
      testcase_Packet pkt = new();
      this.env.blueprint.copy(pkt);
      this.env.blueprint.copy(pkt);

      // Lab 4 - Update scenario generator's blueprint object via using
      foreach (this.env.gen.scenario_set[i])
         this.env.gen.scenario_set[i].using = pkt;

   end
   this.env.run();
`vmm_test_end(one_port)

tb_env env = new();

initial begin
   vmm_test_registry::list();
   vmm_test_registry::run(env);
end

endprogram
