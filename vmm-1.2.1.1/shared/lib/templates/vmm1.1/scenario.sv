//
// Template for VMM-compliant scenario class
//
// <SCEN>       Name of scenario class
// <TR>         Name of transaction descriptor class
// [filename]   scenario
//



class SCEN extends TR_scenario;
   
   int SCEN;
   // ToDo: Change max_length as per requirement
   int max_length = 10;

   extern function new();

   constraint SCEN_valid {
      if(scenario_kind == SCEN) {
         repeated == 0;
           
         // ToDo: Change length as per requirement

         length == 10;
          
         // ToDo: Add scenario specific consrtaints on items here
      }   
   }

endclass: SCEN

function SCEN::new();

   super.new();
   this.SCEN = define_scenario("SCEN",this.max_length);

endfunction: new


