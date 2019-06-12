// Class: vmm_scenario
// Base class for all user-defined scenarios. This class extends from <vmm_data>.
  
// Function: new
// Specifies that an explicit user-defined constructor is used, instead of the default 
// constructor provided by the shorthand macros. Also, declares a <vmm_log> instance 
// that can be passed to the base class constructor. Use this macro when data members 
// must be explicitly initialized in the constructor. The class-name specified must 
// be the name of the vmm_scenario extension class that is being implemented. This macro 
// should be followed by the constructor declaration, and must precede the shorthand 
// data member section. This means that it should be located before the 
// <`vmm_scenario_member_begin()> macro.
  
function vmm_scenario::new(`VMM_SCENARIO parent = null
                           `VMM_SCENARIO_BASE_NEW_ARGS);
   super.new(this.get_vmm_log() `VMM_SCENARIO_BASE_NEW_CALL);
   this.set_parent_scenario(parent);
`ifdef VMM_DATA_BASE
   `vmm_unit_config_rand_int(repeated, repeated, "repeats scenario", 0, DO_ALL)
   `vmm_unit_config_int(repeat_thresh, repeat_thresh, "max threshold value for scenario to repeat", 0, DO_ALL)
`endif

endfunction: new

function string vmm_scenario::this_class_name();
   return "vmm_scenario";
endfunction: this_class_name

function vmm_log vmm_scenario::get_vmm_log();
   return null;
endfunction

// //////////////////////////////////////////// 
// Function: psdisplay 
// 
// Creates human-readable image of the content of the scenario descriptor. 
// 
//|   
//|   class my_scenario extends atm_cell_scenario;
//|      int unsigned START_UP_SEQ;
//|        function new()
//|         redefine_scenario(this.START_UP_SEQ,"WAKE_UP_SEQ",5);
//|         ...
//|      endfunction
//|      ...
//|   endclass
//|   initial begin
//|      ...
//|      my_scenario scen_inst = new();
//|      ...
//|      $display("Data of the redefined scenario is %s \n", 
//|         scen_inst.psdisplay());
//|      ...
//|   end
function string vmm_scenario::psdisplay(string prefix = "");
   int i;

   $sformat(psdisplay,
            "%sScenario \"%s\": kind=%0d, length=%0d (max=%0d), repeated=%0d",
            prefix, this.scenario_name(this.scenario_kind),
            this.scenario_kind, this.length, this.max_length,
            this.repeated);
endfunction: psdisplay

// //////////////////////////////////////////// 
// Function: define_scenario 
// 
// Defines a new scenario kind that is included in this scenario descriptor, and returns
// a unique scenario kind identifier. The scenario_kind data member
// randomly selects one of the defined scenario kinds. The new scenario kind may contain
// up to the specified number of random transactions. 
// The scenario kind identifier should be stored in a state variable that can then be subsequently
// used to specify the kind-specific constraints. 
// 
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   class my_scenario extends atm_cell_scenario;
//|      int unsigned START_UP_SEQ;
//|      int unsigned RESET_SEQ;
//|      ...
//|      function new()
//|         START_UP_SEQ = define_scenario("START_UP_SEQ",5);
//|         RESET_SEQ = define_scenario("RESET_SEQ",11);
//|         ...
//|      endfunction
//|      ...
//|   endclass
function int unsigned vmm_scenario::define_scenario(string name,
                                                    int unsigned max_len = 0);
   define_scenario = this.next_scenario_kind++;
   this.scenario_names[define_scenario] = name;

   if (max_len > this.max_length) this.max_length = max_len;
endfunction: define_scenario

// //////////////////////////////////////////// 
// Function: redefine_scenario 
// 
// Redefines an existing scenario kind, which is included in this scenario descriptor.
// The scenario kind may be redefined with a different name, or maximum number of random
// transactions. 
// Use this method to modify, refine, or replace an existing scenario kind, in a pre-defined
// scenario descriptor. 
// 
//|   
//|   class my_scenario extends atm_cell_scenario;
//|      int unsigned START_UP_SEQ;
//|      ...
//|      function new()
//|         redefine_scenario(this.START_UP_SEQ,"WAKE_UP_SEQ",5);
//|         ...
//|      endfunction
//|      ...
//|   endclass
function void vmm_scenario::redefine_scenario(int unsigned scenario_kind,
                                              string       name,
                                              int unsigned max_len = 0);
   this.scenario_names[scenario_kind] = name;
    if (max_len > this.max_length) this.max_length = max_len;
endfunction: redefine_scenario

// //////////////////////////////////////////// 
// Function: scenario_name 
// 
// Returns the name of the specified scenario kind, as defined by the <define_scenario()
// or redefine_scenario> methods. 
// 
//|   
//|   class my_scenario extends atm_cell_scenario;
//|      int unsigned START_UP_SEQ;
//|      ...
//|      function new()
//|           redefine_scenario(this.START_UP_SEQ,"WAKE_UP_SEQ",5);
//|         ...
//|      endfunction
//|      ...
//|      function post_randomize();
//|         $display("Name of the redefined scenario is %s \n", 
//|            scenario_name(scenario_kind));
//|         ...
//|      endfunction
//|   endclass
function string vmm_scenario::scenario_name(int unsigned scenario_kind = 0);
   if (!this.scenario_names.exists(scenario_kind)) begin
      vmm_log log = this.get_vmm_log();
      if (this.next_scenario_kind == 0 && scenario_kind == 0) begin
         return this.__default_name();
      end
      `vmm_error(log, `vmm_sformatf("Cannot find scenario name: undefined scenario kind %0d",
                                    scenario_kind));
      return "?";
   end

   scenario_name = this.scenario_names[scenario_kind];
endfunction: scenario_name

function string vmm_scenario::__default_name();
   return "Undefined VMM Scenario";
endfunction: __default_name

function int unsigned vmm_scenario::get_max_length();
   return this.max_length;
endfunction: get_max_length

// //////////////////////////////////////////// 
// Function: set_parent_scenario 
// 
// Specifies the single stream or multiple-stream scenario that is the parent of this
// scenario. This allows this scenario to grab a channel that is already grabbed by the
// parent scenario. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      rand int payload[3];
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario parent_scen = new;
//|      atm_cell_scenario child_scen = new;
//|      initial begin
//|         vmm_log(log,"Setting parent to a child scenarion \n");
//|           child.scen.set_parent_scenario(parent_scen);
//|      end
//|   endprogram
function void vmm_scenario::set_parent_scenario(vmm_scenario parent);
   this.parent = parent;
endfunction: set_parent_scenario

// //////////////////////////////////////////// 
// Function: get_parent_scenario 
// 
// Returns the single stream or multiple-stream scenario that was specified as the parent
// of this scenario. A scenario with no parent is a top-level scenario. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      ...
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      ...
//|      atm_cell_scenario parent_scen = new;
//|      atm_cell_scenario child_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         vmm_log(log,"Setting parent to a child scenarion \n");
//|         child.scen.set_parent_scenario(parent_scen);
//|         ...
//|         if(child_scen.get_parent_scenario() == parent_scen)
//|            vmm_log(log,"Child scenario has proper parent \n");
//|            ...
//|         else
//|            vmm_log(log,"Child scenario has improper parent \n");
//|         ...
//|      end
//|   endprogram
function vmm_scenario vmm_scenario::get_parent_scenario();
   return this.parent;
endfunction: get_parent_scenario

function vmm_data vmm_scenario::copy(vmm_data to = null);
   vmm_scenario cpy;

   if (to == null) cpy = new;
   else if (!$cast(cpy, to)) begin
      vmm_log log = this.get_vmm_log();
      `vmm_fatal(log, "Cannot copy to non-vmm_scenario instance");
      return null;
   end

   super.copy_data(cpy);

   cpy.next_scenario_kind = this.next_scenario_kind;
   cpy.max_length         = this.max_length;
   cpy.scenario_names     = this.scenario_names;
   cpy.parent             = this.parent;


   cpy.scenario_kind = this.scenario_kind;
   cpy.length        = this.length;
   cpy.repeated      = this.repeated;

   return cpy;
endfunction: copy
