//
// Template for VMM-compliant multi stream scenario class
// <VNAME>      Name of the VIP
// <TR>         Name of transaction descriptor class 
// [filename]   VNAME_ms_scenario

`ifndef VNAME_MS_SCN__SV
`define VNAME_MS_SCN__SV

class VNAME_ms_scen extends vmm_ms_scenario;
   
  `vmm_typename(VNAME_ms_scen) 
   // Instance of TR class 
   rand TR trans;

  //ToDo : Declare other required transactions here 
  
   extern function new();
   extern virtual function vmm_data allocate();
   extern virtual function vmm_data copy(vmm_data to = null);   
   extern virtual task execute(ref int n);
    
   `vmm_class_factory(VNAME_ms_scen)
endclass: VNAME_ms_scen

 function VNAME_ms_scen::new();
    super.new(null);
    trans = new();
    //ToDo : Instantiate other required transactions here
 endfunction: new

 function vmm_data VNAME_ms_scen::allocate();
    VNAME_ms_scen scn = new;
    allocate = scn;
  endfunction: allocate
  
 function vmm_data VNAME_ms_scen::copy(vmm_data to = null);
   VNAME_ms_scen scn = new;
   scn.stream_id = this.stream_id;
   scn.scenario_id = this.scenario_id;
   //ToDo : Copy other variables if added in the multi stream scenario class 
   copy = scn;
 endfunction: copy

 task VNAME_ms_scen::execute(ref int n);
    fork
       begin
         TR_channel out_chan;
         SING_DRV_START
         $cast(out_chan, this.get_channel("TR_scenario_channel"));
         SING_DRV_END
         MULT_DRV_START
         $cast(out_chan, this.get_channel("TR_scenario_channel_0"));
         MULT_DRV_END
         this.trans.randomize();
         out_chan.put(this.trans.copy());
       end
       begin
         //ToDo: Add the logic for the data injection to other channel
       end  
       //ToDo : Create another threads if more channels of required types need to generate data
    join
    n += 1;   //ToDo: Increment this to the number of channels feeded by this scenario 
 endtask: execute
 
`endif // VNAME_MS_SCN__SV
