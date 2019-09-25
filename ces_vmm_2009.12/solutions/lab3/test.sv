program automatic test;
`include "tb_env.sv"

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

`vmm_test_begin(all_ports, tb_env, "All Ports")
   this.env.cfg.num_of_iports = 16;
   this.env.cfg.num_of_oports = 16;
   this.env.cfg.num_of_iports.rand_mode(0);
   this.env.cfg.num_of_oports.rand_mode(0);
   this.env.build();
   begin
      testcase_Packet pkt = new();
      this.env.blueprint.copy(pkt);
      this.env.gen.randomized_obj = pkt;
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
      this.env.gen.randomized_obj = pkt;
   end
   this.env.run();
`vmm_test_end(one_port)

tb_env env = new();

initial begin
   vmm_test_registry::list();
   vmm_test_registry::run(env);
end

endprogram
