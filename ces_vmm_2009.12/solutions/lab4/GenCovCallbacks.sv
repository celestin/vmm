// Lab 4 - Change Packet_atomic_gen_callbacks to Packet_scenario_gen_callbacks
// ToDo
class GenCovCallbacks extends Packet_scenario_gen_callbacks;

   bit[3:0] sa, da;

   covergroup gen_port_cov;
      coverpoint sa;
      coverpoint da;
      cross sa, da;
      type_option.weight = 0;
   endgroup

   function new();
      this.gen_port_cov = new();
   endfunction

   // Lab 4 - Change post_inst_gen method to post_scenario_gen
   // ToDo
   task post_scenario_gen(Packet_scenario_gen gen, Packet_scenario scenario, ref bit drop);
      if (scenario.length) repeat (scenario.repeated + 1) begin
         foreach (scenario.items[i]) begin
            this.sa = scenario.items[i].sa;
            this.da = scenario.items[i].da;
            this.gen_port_cov.sample();
         end
      end
   endtask

endclass
