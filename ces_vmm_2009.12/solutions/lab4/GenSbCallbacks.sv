typedef class scoreboard;

// Lab 4 - Change Packet_atomic_gen_callbacks to Packet_scenario_gen_callbacks
// ToDo
class GenSbCallbacks extends Packet_scenario_gen_callbacks;


   scoreboard sb;
   function new(scoreboard sb);
      this.sb = sb;
   endfunction

   // Lab 4 - Change post_inst_gen to post_scenario_gen
   // ToDo
   task post_scenario_gen(Packet_scenario_gen gen, Packet_scenario scenario, ref bit drop);
      if (scenario.length) repeat (scenario.repeated + 1) begin
         foreach (scenario.items[i]) begin
            this.sb.deposit(scenario.items[i].copy());
         end
      end
   endtask

endclass
