class test_scenario extends Packet_scenario;
   int unsigned WALKING_ZERO;
   int unsigned WALKING_ONE;

   constraint test {
      // Lab 4 - add constraint for WALKING_ZERO and WALKING_ONE
      // ToDo
      repeated == 0;
      $void(scenario_kind) == WALKING_ONE -> {
         length == 5;
         foreach (items[i]) {
            foreach(items[i].payload[j]) {
               items[i].payload[j] == 8'h1 << (j%8);
            }
         }
      }
      $void(scenario_kind) == WALKING_ZERO -> {
         length == 5;
         foreach (items[i]) {
            foreach(items[i].payload[j]) {
               items[i].payload[j] == ~(8'h1 << (j%8));
            }
         }
      }
   }

   function new();
      // Lab 4 - add define_scenario for WALKING_ZERO and WALKING_ONE
      // ToDo
      this.WALKING_ZERO = define_scenario("Walking 0's", 5);
      this.WALKING_ONE  = define_scenario("Walking 1's", 5);
   endfunction
endclass
