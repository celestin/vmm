//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

function vmm_ss_scenario_base::new(`VMM_SCENARIO parent = null `VMM_SCENARIO_NEW_ARGS); 
	super.new(parent `VMM_SCENARIO_NEW_CALL); 
endfunction

function void vmm_ss_scenario_base::Xset_allocate_idX(vmm_data tr, int idx = -1);
endfunction

 
`ifndef NO_VMM12_PARAM_CHANNEL
function string vmm_ss_scenario::this_class_name(); 
   return $typename(this);
endfunction: this_class_name 
 
function vmm_log vmm_ss_scenario::get_vmm_log(); 
   return this.log; 
endfunction 
 
function string vmm_ss_scenario::__default_name(); 
   return {"Undefined ", $typename(T), " Scenario"}; 
endfunction: __default_name 
 
function string vmm_ss_scenario::psdisplay(string prefix = ""); 
   psdisplay = super.psdisplay(prefix); 
   foreach (this.items[i]) begin 
      string pfx; 
      if (this.items[i] == null) continue; 
      $sformat(pfx, "%s  Item[%0d]: ", prefix, i); 
      psdisplay = {psdisplay, "\n", this.items[i].psdisplay(pfx)}; 
   end 
   if (this.using != null) begin 
      psdisplay = {psdisplay, "\n", this.using.psdisplay({prefix, "  Using: "})}; 
   end 
   return psdisplay; 
endfunction 

constraint vmm_ss_scenario::`vmm_scenario_valid_(T) { 
   items.size() == length; 
 
`ifdef VMM_SOLVE_BEFORE_SIZE 
   solve length before items.size `VMM_SOLVE_BEFORE_OPT; 
`endif 
} 

function vmm_ss_scenario::new(`VMM_SCENARIO_NEW_ARGS); 
   super.new(null `VMM_SCENARIO_NEW_CALL); 
   using = null; 
endfunction: new 
 
function vmm_data vmm_ss_scenario::copy(vmm_data to = null); 

   vmm_ss_scenario#(T, channel_name) cpy; 
 
   if (to == null) cpy = new(); 
   else if (!$cast(cpy, to)) begin 
      //`vmm_fatal(this.log, {"Cannot copy to non-", `VMM_MACRO_TO_STRING(`vmm_scenario_(T)), " instance"}); 
      `vmm_fatal(this.log, {"Cannot copy to non-", `VMM_MACRO_TO_STRING(vmm_ss_scenario#(T, channel_name)), " instance"}); 
      return null; 
   end 
 
   void'(super.copy(cpy)); 
   cpy.items = new [this.items.size()]; 
   foreach (this.items[i]) begin 
      if (this.items[i] == null) cpy.items[i] = null; 
      else $cast(cpy.items[i], this.items[i].copy()); 
   end 
   if (this.using == null) cpy.using = null; 
   else $cast(cpy.using, this.using.copy()); 
 
   return cpy; 

endfunction: copy 
 
function void vmm_ss_scenario::Xset_allocate_idX(vmm_data tr, int idx=-1);
   T itm;
   if (!$cast(itm, tr)) begin
      `vmm_trace(log, "Type mismatch.. Unable to set the factory for the scenario items");
      return;
   end
   if (idx < 0) begin
      allocate_scenario(itm);
   end
   else if (idx >= this.get_max_length()) begin
      `vmm_fatal(log, `vmm_sformatf("item index %0d is greater than max scenario length %0d, unable to allocate factory item for this index", idx, this.get_max_length()));
   end
   else if (idx >= this.items.size()) begin
     T tmp_itm;
     this.items = new [idx+1] (this.items); 
   end
   this.items[idx]             = itm;
   this.items[idx].stream_id   = this.stream_id; 
   this.items[idx].scenario_id = this.scenario_id; 
   this.items[idx].data_id     = idx; 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
   `VMM_OBJECT_SET_PARENT(this.items[idx], this) 
`endif
`endif

endfunction

function void vmm_ss_scenario::allocate_scenario(T using = null); 

   this.items = new [this.get_max_length()]; 
   foreach (this.items[i]) begin 
      if (using == null) this.items[i] = new; 
      else $cast(this.items[i], using.copy()); 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(this.items[i], this) 
`endif
`endif
 
      this.items[i].stream_id   = this.stream_id; 
      this.items[i].scenario_id = this.scenario_id; 
      this.items[i].data_id     = i; 
   end 

endfunction: allocate_scenario 
 
function void vmm_ss_scenario::fill_scenario(T using = null); 

   int i; 
 
   if (this.items.size() < this.get_max_length()) begin 
      this.items = new [this.get_max_length()] (this.items); 
   end 
   foreach (this.items[i]) begin 
      if (this.items[i] != null) continue; 
 
      if (using == null) this.items[i] = new; 
      else $cast(this.items[i], using.copy()); 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(this.items[i], this) 
`endif
`endif
 
      this.items[i].stream_id   = this.stream_id; 
      this.items[i].scenario_id = this.scenario_id; 
      this.items[i].data_id     = i; 
   end 

endfunction: fill_scenario 
 
function void vmm_ss_scenario::pre_randomize(); 
   this.fill_scenario(this.using); 
   this.tmp_items.delete;
   this.tmp_items = new [this.items.size()] (this.items);
endfunction: pre_randomize 

function void vmm_ss_scenario::post_randomize();
   int n_lost_items = this.tmp_items.size() - this.items.size();
   if (n_lost_items > 0) begin
      int tmp_items_size = this.tmp_items.size();
      for (int i = tmp_items_size - 1; i >= tmp_items_size - n_lost_items; --i) begin
         this.tmp_items[i].kill_object();
      end
   end
   this.tmp_items.delete;
endfunction: post_randomize

 
task vmm_ss_scenario::apply(channel_name channel, 
                   ref int unsigned n_insts); 

   int i; 
 
   for (i = 0; i < this.length; i++) begin 
      T item; 
      $cast(item, this.items[i].copy()); 
      channel.wait_for_request();
`ifndef VMM_GRAB_DISABLED 
      channel.put(item,,this); 
`else 
      channel.put(item); 
`endif 
   end 
 
   n_insts = this.length; 

endtask: apply 

function vmm_inject_item_scenario::new(T obj `VMM_DATA_NEW_ARGS); 
   super.new(`VMM_DATA_NEW_CALL); 
 
   this.items    = new [1]; 
   this.items[0] = obj; 
   this.length   = 1; 
   this.repeated = 0; 
   void'(this.define_scenario("Directed 'inject_obj()' transaction", 1)); 
endfunction: new 
 
task vmm_inject_item_scenario::apply(channel_name channel, 
                   ref int unsigned n_insts); 
   channel.wait_for_request();
`ifndef VMM_GRAB_DISABLED 
   channel.put(this.items[0],,this); 
`else 
   channel.put(this.items[0]); 
`endif 
   n_insts = 1; 
endtask: apply 
 
function vmm_atomic_scenario::new(`VMM_DATA_NEW_ARGS); 
   super.new(`VMM_DATA_NEW_CALL); 
   this.ATOMIC = this.define_scenario("Atomic", 1); 
   this.scenario_kind   = this.ATOMIC; 
   this.length = 1; 
endfunction: new 

task vmm_atomic_scenario::apply(channel_name     channel, 
                   ref int unsigned n_insts); 
   super.apply(channel, n_insts); 
endtask: apply 
 
task vmm_scenario_gen_callbacks::pre_scenario_randomize(vmm_scenario_gen #(T, text, channel_name) gen, 
                                    ref vmm_ss_scenario#(T, channel_name) scenario); 
endtask 
 
task vmm_scenario_gen_callbacks::post_scenario_gen(vmm_scenario_gen #(T, text, channel_name) gen, 
                               vmm_ss_scenario#(T, channel_name) scenario, 
                               ref bit                    dropped); 
endtask 
 
`endif //NO_VMM12_PARAM_CHANNEL
function vmm_scenario_gen_base::new(string       name, 
             string       inst, 
             int          stream_id = -1
             `VMM12_XACTOR_NEW_ARGS `VMM_XACTOR_NEW_ARGS); 

   super.new(name, inst, stream_id 
             `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL); 
endfunction

function void vmm_scenario_gen_base::replace_scenario(string name, 
                                        vmm_ss_scenario_base scenario); 
endfunction: replace_scenario 

function void vmm_scenario_gen_base::register_scenario(string name, 
                                        vmm_ss_scenario_base scenario); 
endfunction: register_scenario 

function bit vmm_scenario_gen_base::scenario_exists(string name); 
         return  0; 
endfunction: scenario_exists 

function vmm_ss_scenario_base vmm_scenario_gen_base::Xget_scenarioX(string name); 
endfunction: Xget_scenarioX

// //////////////////////////////////////////// 
// Class: vmm_scenario_gen_base
//
// Basis for Parameterized version of the VMM scenario generator.

// //////////////////////////////////////////// 
// Function: get_n_insts 
// 
// The generator stops after the stop_after_n_insts limit on the number of instances
// is reached, and only after entire scenarios are applied. Hence, it can generate a few
// more instances than configured. This method returns the actual number of instances
// that were generated. 
// 
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      initial
//|      begin
//|         atm_gen.stop_after_n_insts = 10;
//|         atm_gen.start_xactor();
//|         `vmm_note(log,$psprintf(
//|            "Total Instances Generated: %0d",
//|            atm_gen.get_n_insts()));  
//|      end
//|   endprogram
function int unsigned vmm_scenario_gen_base::get_n_insts(); 
   get_n_insts = this.inst_count; 
endfunction: get_n_insts 
 
// //////////////////////////////////////////// 
// Function: get_n_scenarios 
// 
// The generator stops after the stop_after_n_scenarios limit on the number of scenarios
// is reached, and only after entire scenarios are applied. Hence, it can generate a few
// less scenarios than configured. This method returns the actual number of scenarios
// that were generated. 
// 
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      initial
//|      begin
//|         atm_gen.stop_after_n_scenarios = 10;
//|         atm_gen.start_xactor();
//|         `vmm_note(log,$psprintf("Total Scenarios Generated: 
//|             %0d", atm_gen.get_n_scenarios()));             
//|      end
//|      ...
//|   endprogram
function int unsigned vmm_scenario_gen_base::get_n_scenarios(); 
   get_n_scenarios = this.scenario_count; 
endfunction: get_n_scenarios 

`ifndef NO_VMM12_PARAM_CHANNEL

// //////////////////////////////////////////// 
// Class: vmm_scenario_gen
//
// Parameterized version of the VMM scenario generator.

// //////////////////////////////////////////// 
// Function: replace_scenario 
// 
// Registers the specified scenario under the specified name, replacing the scenario
// that is previously registered under that name, if any. The name under which a scenario
// is registered does not need to be the same as the name of a kind of scenario, which is defined
// in the scenario descriptor using the <define_scenario> method.
// The same scenario may be registered multiple times under different names, therefore
// creating an alias to the same scenario. 
// Registering a scenario implicitly appends it to the scenario set, if it is not already
// in the scenario_set[$] array. The replaced scenario is removed
// from the scenario set, if it is not also registered under another name. 
// 
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario parent_scen = new;
//|      ...
//|      initial begin
//|        ...
//|         atm_gen.register_scenario("MY SCENARIO", parent_scen);
//|         atm_gen.register_scenario("PARENT SCEN", parent_scen);
//|       ...
//|       if(atm_gen.scenario_exists("MY SCENARIO") 
//|          begin
//|             atm_gen.replace_scenario(
//|                "MY SCENARIO", parent_scen);
//|             vmm_log(log,
//|                "Scenario exists and has been replaced\n");
//|             ...
//|         end
//|      end
//|   endprogram
function void vmm_scenario_gen::replace_scenario(string name, 
                                                 vmm_ss_scenario_base scen); 
   vmm_ss_scenario#(T, channel_name) scenario;
   $cast(scenario, scen);
   if(name == "") begin 
      `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
      return; 
   end 

   if(scenario == null) begin 
      `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); 
      return; 
   end 

   if(!this.scenario_registry.exists(name)) begin 
      `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_scenario]", name)); 
      return ; 
   end 

   foreach(this.scenario_set[i]) begin 
     if(this.scenario_set[i] == this.scenario_registry[name]) begin 
         this.scenario_set.delete(i); 
         break; 
      end 
   end 
   this.scenario_registry[name] = scenario; 
   foreach(this.scenario_set[i]) begin 
       if(this.scenario_set[i] == scenario) 
           return; 
   end 
   this.scenario_set.push_back(scenario); 
endfunction: replace_scenario 

// //////////////////////////////////////////// 
// Function: register_scenario 
// 
// Registers the specified scenario under the specified name. The name under which a scenario
// is registered does not need to be the same as the name of a kind of scenario, which is defined
// in the scenario descriptor using the <define_scenario> method.
// The same scenario may be registered multiple times under different names, therefore
// creating an alias to the same scenario. 
// Registering a scenario implicitly appends it to the scenario set, if it is not already
// in the scenario_set[$] array. 
// It is an error to register a scenario under a name that already exists. Use the <replace_scenario>
// method to replace a registered scenario. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      ...
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario parent_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering scenario \n");
//|           atm_gen.register_scenario("PARENT SCEN", parent_scen);
//|         ...
//|      end
//|   endprogram
function void vmm_scenario_gen::register_scenario(string name, 
                                        vmm_ss_scenario_base scen); 
   vmm_ss_scenario#(T, channel_name) scenario;
   $cast(scenario, scen);
   if(name == "") begin 
      `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
      return; 
   end 

   if(this.scenario_registry.exists(name)) begin 
      `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the scenario registry", name)); 
      return; 
   end 

   if(scenario == null) begin 
      `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name)); 
      return; 
   end 

   this.scenario_registry[name] = scenario; 

   foreach(this.scenario_set[i]) begin 
      if(this.scenario_set[i] == scenario) 
         return; 
   end 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
   `VMM_OBJECT_SET_PARENT(scenario, this) 
`endif
`endif
   this.scenario_set.push_back(scenario); 
endfunction: register_scenario 

// //////////////////////////////////////////// 
// Function: scenario_exists 
// 
// Returns TRUE, if there is a scenario registered under the specified name. Otherwise,
// it returns FALSE. 
// Use the <get_scenario> method to retrieve a scenario under a specified
// name. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      ...
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario parent_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering scenario \n");
//|         atm_gen.register_scenario("PARENT SCEN", parent_scen);
//|         ...
//|         if(atm_gen.scenario_exists("PARENT SCEN") begin
//|            vmm_log(log,"Scenario exists and you can use \n");
//|            ...
//|         end
//|      end
//|   endprogram
function bit vmm_scenario_gen::scenario_exists(string name); 
     if(name == "") begin 
         `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
         return 0; 
     end 

     if(this.scenario_registry.exists(name)) 
         scenario_exists = 1; 
     else 
         scenario_exists = 0; 
 endfunction: scenario_exists 

function vmm_ss_scenario_base vmm_scenario_gen::Xget_scenarioX(string name); 
   if(name == "") begin 
      `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name)); 
      return null; 
   end 
   if(!this.scenario_registry.exists(name)) begin 
      `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the scenario registry", name)); 
      return null; 
   end 

   Xget_scenarioX = this.scenario_registry[name]; 
   if(Xget_scenarioX == null) 
      `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario associated with it in the scenario registry", name)); 

endfunction: Xget_scenarioX

function string vmm_scenario_gen::psdisplay(string prefix = ""); 
   psdisplay = super.psdisplay(prefix); 
   $sformat(psdisplay, "%s [stops after #insts %0d>%0d or #scenarios %0d>%0d]", 
            psdisplay, this.inst_count, this.stop_after_n_insts, 
            this.scenario_count, this.stop_after_n_scenarios); 
   $sformat(psdisplay, "%sn%sOutChan: %s(%s) [level=%0d of %0d]", 
            psdisplay, prefix, this.out_chan.log.get_name(), 
            this.out_chan.log.get_instance(), this.out_chan.level(), 
            this.out_chan.full_level()); 
   foreach (this.scenario_registry[name]) begin 
      psdisplay = {psdisplay, "n", 
                   this.scenario_registry[name].psdisplay(prefix)}; 
   end 
   return psdisplay; 
endfunction: psdisplay 
 
// //////////////////////////////////////////// 
// Function: new 
// 
// Creates a new instance of a scenario generator transactor, with the specified instance
// name and optional stream identifier. The generator can be optionally connected to
// the specified output channel. If no output channel is specified, one will be created
// internally in the class-name_scenario_gen::out_chan property. 
// The name of the transactor is defined as the user-defined class description string,
// which is specified in the class implementation macro appended with the Scenario
// Generator. Specified parent argument indicates the parent of this generator. 
// 
//|   
//|   program test_scenario;
//|      ...
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|   endprogram
function vmm_scenario_gen::new(string       inst, 
             int          stream_id = -1, 
             channel_name out_chan  = null 
             `VMM12_XACTOR_NEW_ARGS `VMM_XACTOR_NEW_ARGS); 

   super.new({text, " Scenario Generator"}, inst, stream_id 
             `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL); 

 
   if (out_chan == null) begin 
      out_chan = new({text, " Scenario Generator output channel"}, 
                     inst); 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_CHANNEL
      `VMM_OBJECT_SET_PARENT(out_chan, this) 
`endif
`endif
   end 
   this.out_chan = out_chan; 
   this.out_chan.set_producer(this); 
   this.log.is_above(this.out_chan.log); 
 
   this.scenario_count = 0; 
   this.inst_count = 0; 
   this.stop_after_n_insts     = 0; 
   this.stop_after_n_scenarios = 0; 
 
   this.select_scenario = new; 
   begin 
      vmm_atomic_scenario#(T, text, channel_name) sc = new; 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(sc, this) 
`endif
`endif
      this.register_scenario("Atomic", sc); 
   end 
 
   void'(this.notify.configure(GENERATED)); 
   void'(this.notify.configure(DONE, vmm_notify::ON_OFF)); 
endfunction: new 
 

// //////////////////////////////////////////// 
// Function: get_all_scenario_names 
// 
// Appends the names under which a scenario descriptor is registered. Returns the number
// of names that were added to the array. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      ...
//|   endclass
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   program test_scenario;
//|      string scen_names_arr[$];
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario atm_scenario = new;
//|      ...
//|      initial begin
//|         ...
//|         atm_gen.get_all_scenario_names(scen_names_arr);
//|      end
//|   endprogram
function void vmm_scenario_gen::get_all_scenario_names(ref string name[$]); 
   string s; 

   if(this.scenario_registry.first(s)) begin 
      do begin 
         name.push_back(s); 
      end while(this.scenario_registry.next(s)); 
   end 
   if(name.size() == 0) begin 
      `vmm_warning(this.log, "There are no entries in the scenario generator registry"); 
   end 
endfunction: get_all_scenario_names 

// //////////////////////////////////////////// 
// Function: get_names_by_scenario 
// 
// Appends the names under which the specified scenario descriptor is registered. Returns
// the number of names that were added to the array. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|   endclass
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   program test_scenario;
//|      string scen_names_arr[$];
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario atm_scenario = new;
//|      initial begin
//|         atm_gen.get_names_by_scenario(
//|            atm_scenario,scen_names_arr);
//|      end
//|   endprogram
function void vmm_scenario_gen::get_names_by_scenario(vmm_ss_scenario_base scenario, 
                                            ref string name[$]); 
   string s; 

   if(scenario == null) begin 
      `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); 
      return; 
   end 

   if(this.scenario_registry.first(s)) begin 
      do begin 
         if(this.scenario_registry[s] == scenario) 
            name.push_back(s); 
      end while(this.scenario_registry.next(s)); 
   end 
   if(name.size() == 0) begin 
      `vmm_warning(this.log, "There are no entries in the scenario registry"); 
   end 
endfunction: get_names_by_scenario 

// //////////////////////////////////////////// 
// Function: get_scenario_name 
// 
// Returns a name under which the specified scenario descriptor is registered. Returns
// "", if the scenario is not registered. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario atm_scenario = new;
//|      initial begin
//|         scenario_name = atm_gen.get_scenario_name(atm_scenario);
//|         vmm_note(log,`vmm_sformatf("Registered name for atm_scenario is : %s\n",scenario_name));
//|      end
//|   endprogram
function string vmm_scenario_gen::get_scenario_name(vmm_ss_scenario#(T, channel_name) scenario); 
     string s[$]; 

     if(scenario == null) begin 
         `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); 
         return ""; 
     end 

     this.get_names_by_scenario(scenario, s); 

     if(s.size()) 
         get_scenario_name = s[0]; 
     else 
         get_scenario_name = ""; 
endfunction: get_scenario_name 

// //////////////////////////////////////////// 
// Function: get_scenario_index 
// 
// Returns the index of the specified scenario descriptor, which is in the scenario set
// array. A warning message is generated and returns -1, if the scenario descriptor is
// not found in the scenario set. 
// 
//|   
//|   class atm_cell extends vmm_data;
//|      ...
//|   endclass
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario atm_scenario = new;
//|      ...
//|      initial begin
//|         ...
//|         scen_index = atm_gen.get_scenario_index(atm_scenario);
//|         if(scen_index == 5)
//|            `vmm_note(log, `vmm_sformatf(
//|               "INDEX MATCHED %0d", index));
//|         else
//|            `vmm_error(log,`vmm_sformatf(
//|               "INDEX NOT MATCHING %0d", index));
//|         ...
//|      end
//|   endprogram
function int vmm_scenario_gen::get_scenario_index(vmm_ss_scenario_base scenario); 
    get_scenario_index = -1; 
    foreach(this.scenario_set[i]) begin 
       if(this.scenario_set[i] == scenario) begin 
          return (get_scenario_index = i); 
       end 
    end 
    if(get_scenario_index == -1) begin 
       `vmm_warning(this.log, `vmm_sformatf("Cannot find the index for the scenario")); 
    end 
endfunction: get_scenario_index 

// //////////////////////////////////////////// 
// Function: unregister_scenario 
// 
// Completely unregisters the specified scenario descriptor and returns TRUE, if it
// exists in the registry. The unregistered scenario is also removed from the scenario
// set. 
// 
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_scenario;
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_scenario atm_scenario = new;
//|       ...
//|      initial begin
//|         if(atm_gen.unregister_scenario(atm_scenario))
//|            vmm_log(log,"Scenario has been unregistered \n");
//|         else
//|            vmm_log(log,"Unable to unregister scenario\n");
//|      end
//|   endprogram
function bit vmm_scenario_gen::unregister_scenario(vmm_ss_scenario_base scenario); 
   string s; 
   unregister_scenario=0; 

   if(scenario == null) begin 
      `vmm_error(this.log, `vmm_sformatf("scenario is a null value")); 
      return 0; 
   end 
   if(this.scenario_registry.first(s)) begin 
      do begin 
         if(this.scenario_registry[s] == scenario) begin 
            this.scenario_registry.delete(s); 
            unregister_scenario=1; 
         end 
      end while(this.scenario_registry.next(s)); 
   end 
   if(unregister_scenario==0) begin 
      `vmm_warning(this.log, "There are no entries in the scenario registry"); 
   end 
   if(unregister_scenario) begin 
      foreach(this.scenario_set[i]) begin 
         if(this.scenario_set[i] == scenario) begin 
            this.scenario_set.delete(i); 
            break; 
         end 
      end 
   end 
endfunction: unregister_scenario 

// //////////////////////////////////////////// 
// 
// Task: inject_obj 
// 
// Unlike injecting the descriptor directly in the output channel, it counts toward the
// number of instances and scenarios generated by this generator, and will be subjected
// to the callback methods as an atomic scenario. The method returns once the descriptor
// is consumed by the output channel, or it is dropped by the callback methods. 
// This method can be used to inject directed stimulus while the generator is running (with
// unpredictable timing), or when the generated is stopped. 
// 
//|   
//|   program test_scenario;
//|      ...
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12, genchan);
//|      atm_cell tr = new();
//|      ...
//|      initial
//|      begin
//|         ...
//|         tr.addr = 64'ha0;
//|         tr.data = 64'h50;
//|         atm_gen.stop_after_n_scenarios = 10;
//|         atm_gen.start_xactor();
//|         ...  
//|         atm_gen.inject_obj(tr);
//|         ...
//|      end
//|      ...
//|   endprogram
task vmm_scenario_gen::inject_obj(T obj); 
   //`vmm_inject_item_scenario_(T) scenario = new(obj); 
   vmm_inject_item_scenario#(T, text, channel_name) scenario = new(obj); 
   this.inject(scenario); 
endtask: inject_obj 
 
// //////////////////////////////////////////// 
// 
// Task: inject 
// 
// Unlike injecting the descriptors directly in the output channel, it counts toward
// the number of instances and scenarios generated by this generator, and will be subjected
// to the callback methods. The method returns once the scenario is consumed by the output
// channel, or it is dropped by the callback methods. 
// This method can be used to inject directed stimulus while the generator is running (with
// unpredictable timing), or when the generated is stopped. 
// 
//|   
//|   class my_scenario extends atm_cell_scenario
//|      ...
//|      virtual task apply(atm_cell_channel channel,
//|            ref int unsigned n_insts);
//|         ...
//|         this.randomize();
//|         super.apply(channel, n_insts);
//|         ...
//|      endtask
//|   ...
//|   endclass
//|   
//|   program test_scenario;
//|      ...
//|      atm_cell_scenario_gen atm_gen = 
//|         new("Atm Scenario Gen", 12);
//|      my_scenario scen;
//|      ...
//|      initial
//|      begin
//|         ...
//|         atm_gen.stop_after_n_scenarios = 10;
//|         atm_gen.start_xactor();
//|         ...          
//|         atm_gen.inject(scen);
//|         ...
//|      end
//|      ...
//|   endprogram
task vmm_scenario_gen::inject(vmm_ss_scenario#(T, channel_name) scenario); 
   bit drop = 0; 
 
   scenario.stream_id   = this.stream_id; 
   scenario.scenario_id = this.scenario_count; 
   foreach (scenario.items[i]) begin 
      scenario.items[i].stream_id   = scenario.stream_id; 
      scenario.items[i].scenario_id = scenario.scenario_id; 
      scenario.items[i].data_id     = i; 
   end 
 
   `vmm_callback(vmm_scenario_gen_callbacks#(T, text, channel_name),post_scenario_gen(this, scenario, drop)); 
 
   if (!drop) begin 
      this.scenario_count++; 
      this.notify.indicate(GENERATED, scenario); 
 
      if (scenario.repeated > scenario.repeat_thresh) begin 
         `vmm_warning(this.log, `vmm_sformatf("A scenario will be repeated %0d times...", 
                                              scenario.repeated)); 
      end 
      repeat (scenario.repeated + 1) begin 
         int unsigned n_insts = 0; 
         scenario.apply(this.out_chan, n_insts); 
         this.inst_count += n_insts; 
      end 
   end 
endtask: inject 
 
function void vmm_scenario_gen::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST); 
   super.reset_xactor(rst_typ); 
   this.scenario_count = 0; 
   this.inst_count     = 0; 
   this.out_chan.flush(); 
   `vmm_delQ(this.select_scenario.last_selected); 
 
   if (rst_typ >= FIRM_RST) begin 
      this.notify.reset( , vmm_notify::HARD); 
   end 
 
   if (rst_typ >= HARD_RST) begin 
      vmm_atomic_scenario#(T, text, channel_name) sc = new; 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(sc, this) 
`endif
`endif
 
      this.stop_after_n_insts     = 0; 
      this.stop_after_n_scenarios = 0; 
      this.select_scenario = new; 
      this.scenario_set.push_back(sc); 
   end 
 
endfunction: reset_xactor 
 
function void vmm_scenario_gen::start_xactor(); 
`ifdef VMM12_XACTOR_BASE
    `vmm_unit_config_int(stop_after_n_scenarios, stop_after_n_scenarios, "runs number of scenarios", 0, DO_ALL)
    `vmm_unit_config_int(stop_after_n_insts, stop_after_n_insts, "runs number of instances", 0, DO_ALL)
`endif
    super.start_xactor();
endfunction: start_xactor 
 
task vmm_scenario_gen::main(); 
   vmm_ss_scenario#(T, channel_name) the_scenario; 
 
   fork 
      super.main(); 
   join_none 
 
   if(this.scenario_set.size() == 0) 
       return; 
 
   while ((this.stop_after_n_insts <= 0 
           || this.inst_count < this.stop_after_n_insts) 
          && (this.stop_after_n_scenarios <= 0 
              || this.scenario_count < this.stop_after_n_scenarios)) begin 
 
      this.wait_if_stopped(); 
 
      this.select_scenario.stream_id    = this.stream_id; 
      this.select_scenario.scenario_id  = this.scenario_count; 
      this.select_scenario.n_scenarios  = this.scenario_set.size(); 
      this.select_scenario.scenario_set = this.scenario_set; 
      if (this.select_scenario.last_selected.size() == 0) 
         this.select_scenario.next_in_set = 0; 
      else 
         this.select_scenario.next_in_set = ((this.select_scenario.last_selected[$] + 1) % this.scenario_set.size()); 
 
      if (!this.select_scenario.randomize()) begin 
         `vmm_fatal(this.log, "Cannot select scenario descriptor"); 
         continue; 
      end 
 
      if (this.select_scenario.select < 0 || 
          this.select_scenario.select >= this.scenario_set.size()) begin 
         `vmm_fatal(this.log, `vmm_sformatf("Select scenario #%0d is not within available set (0-%0d)", 
                                            this.select_scenario.select, 
                                            this.scenario_set.size()-1)); 
         continue; 
      end 
 
      this.select_scenario.last_selected.push_back(this.select_scenario.select); 
      while (this.select_scenario.last_selected.size() > 10) begin 
         void'(this.select_scenario.last_selected.pop_front()); 
      end 
 
      the_scenario = this.scenario_set[this.select_scenario.select]; 
      if (the_scenario == null) begin 
         `vmm_fatal(this.log, `vmm_sformatf("Selected scenario #%0d does not exist", 
                                            this.select_scenario.select)); 
         continue; 
      end 
 
      the_scenario.stream_id   = this.stream_id; 
      the_scenario.scenario_id = this.scenario_count; 
      foreach (the_scenario.items[i]) begin 
         if (the_scenario.items[i] == null) continue; 
 
         the_scenario.items[i].stream_id   = the_scenario.stream_id; 
         the_scenario.items[i].scenario_id = the_scenario.scenario_id; 
         the_scenario.items[i].data_id     = i; 
      end 
 
      `vmm_callback(vmm_scenario_gen_callbacks#(T, text, channel_name), 
                    pre_scenario_randomize(this, the_scenario)); 
      if (the_scenario == null) continue; 
 
      if (!the_scenario.randomize()) begin 
         `vmm_fatal(this.log, $psprintf("Cannot randomize scenario descriptor #%0d", 
                                        this.select_scenario.select)); 
         continue; 
      end 
      this.inject(the_scenario); 
   end 
 
   this.notify.indicate(DONE); 
   this.notify.indicate(XACTOR_STOPPED); 
   this.notify.indicate(XACTOR_IDLE); 
   this.notify.reset(XACTOR_BUSY); 
endtask: main 
  
`endif //NO_VMM12_PARAM_CHANNEL

