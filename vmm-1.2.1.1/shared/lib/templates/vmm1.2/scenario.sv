//
// Template for VMM-compliant scenario class
//
// <SCEN>       Name of scenario class
// <TR>         Name of transaction descriptor class
// [filename]   scenario
//



class SCEN extends TR_scenario;
  
  `vmm_typename(SCEN) 
   int SCN;
   // ToDo: Change max_length as per requirement
   int max_length = 10;

   constraint SCEN_valid {
      if(scenario_kind == SCN) {
         repeated == 0;
           
         // ToDo: Change length as per requirement

         length == 10;
          
         // ToDo: Add scenario specific consrtaints on items here
      }   
   }
   extern function new();
   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);

  `vmm_class_factory(SCEN)
endclass: SCEN

function SCEN::new();
   super.new();
   this.SCN = define_scenario("SCEN",this.max_length);
endfunction: new

function vmm_data SCEN::allocate();
   SCEN scn = new;
   allocate = scn;
endfunction

function vmm_data SCEN::copy(vmm_data to = null);
   SCEN scn = new;
   scn.stream_id = this.stream_id;
   scn.scenario_id = this.scenario_id;
   scn.max_length  = this.max_length;
   //ToDo : Copy other variables if added in the scenario class  
   copy = scn;
endfunction

