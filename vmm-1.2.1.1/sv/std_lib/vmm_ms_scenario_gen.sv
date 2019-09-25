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


// //////////////////////////////////////////// 
// Class: vmm_ms_scenario
//
// This is a base class for all user-defined multi-stream scenario descriptors. 
// This class extends from <vmm_scenario>.
//
// Function: new 
// 
// Creates a new instance of a multi-stream scenario descriptor. 
// If a parent scenario descriptor is specified, then this instance of a multi-stream
// scenario descriptor is assumed to be instantiated inside the specified scenario descriptor,
// creating a hierarchical multi-stream scenario descriptor. 
// If no parent scenario descriptor is specified, then it is assumed to be a top-level scenario
// descriptor. 
// 
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      function new;
//|         super.new(null);
//|      endfunction: new
//|   endclass
//|   program test;
//|      my_scenario sc0 = new;
//|   endprogram
function vmm_ms_scenario::new(`VMM_SCENARIO parent = null
                              `VMM_SCENARIO_NEW_ARGS);
    super.new(parent `VMM_SCENARIO_NEW_CALL);
endfunction: new


function string vmm_ms_scenario::this_class_name();
   return "vmm_ms_scenario";
endfunction: this_class_name


function vmm_log vmm_ms_scenario::get_vmm_log();
   return this.log;
endfunction


function string vmm_ms_scenario::__default_name();
   return "Undefined VMM Multi-Stream Scenario";
endfunction: __default_name



// //////////////////////////////////////////// 
// Task: execute 
// 
// Execute the scenario. Increments the argument "n" by the total number of transactions
// that were executed in this scenario. 
// This method must be overloaded to procedurally define a multi-stream scenario. 
// 
//|   
//|   class my_scenario extends vmm_ms_scenario;
//|      my_atm_cell_scenario atm_scenario;
//|      my_cpu_scenario cpu_scenario;
//|      ...
//|      function new;
//|         super.new(null);
//|         atm_scenario = new;
//|         cpu_scenario = new;
//|      endfunction: new
//|   
//|      task execute(ref int n);
//|         fork
//|           begin
//|              atm_cell_channel out_chan;
//|              int unsigned nn = 0;
//|              $cast(out_chan, this.get_channel( 
//|                   "ATM_SCENARIO_CHANNEL"));
//|              atm_scenario.randomize with {length == 1;};
//|              atm_scenario.apply(out_chan, nn);
//|              n += nn;
//|           end
//|           begin
//|              cpu_channel out_chan;
//|              int unsigned nn = 0;
//|              $cast(out_chan,this.get_channel(
//|                  "CPU_SCENARIO_CHANNEL"));
//|              cpu_scenario.randomize with {length == 1;};
//|              cpu_scenario.apply(out_chan, nn);
//|              n += nn;
//|           end
//|         join
//|      endtask: execute
//|      ...
//|   endclass: my_scenario
task vmm_ms_scenario::execute(ref int n);
   vmm_ms_scenario_gen gen = this.get_context_gen();
   vmm_log log = this.get_vmm_log();

   if (gen != null) log = gen.log;


   `vmm_error(log, {"You need to define the vmm_ms_scenario::execute() AND vmm_ms_scenario::copy() methods to implement multi-stream scenario '", this.scenario_name(), "'"});
endtask: execute



function void vmm_ms_scenario::Xset_context_genX(vmm_ms_scenario_gen gen);
   vmm_ms_scenario_gen g;
   if (gen == null) begin
      // Clear context when unregistered
      this.context_scenario_gen = null;
      return;
   end
   g = this.get_context_gen();
   if (g!= null && this.context_scenario_gen != gen) begin
      `vmm_warning(gen.log, `vmm_sformatf("Multi-stream scenario appears to have already been registered with multi-stream scenario generator %s(%s)", g.log.get_name(), g.log.get_instance()));
   end
   this.context_scenario_gen = gen;
endfunction: Xset_context_genX


// //////////////////////////////////////////// 
// Class: vmm_ms_scenario_gen
//
// This class is a pre-defined multi-stream scenario generator.
//
// VMM provides this class to model general purpose scenarios. It is possible to generate 
// heterogeneous scenarios, and have them controlled by a unique transactor.
//
//  The multi-stream scenario generation mechanism provides an efficient way of generating 
// and synchronizing stimulus to various BFMs. This helps you to reuse block level 
// scenarios in subsystem and system levels, and controlling or synchronizing the 
// execution of those scenarios of same or different streams. Single stream scenarios 
// can also be reused in multi-stream scenarios. vmm_ms_scenario and vmm_ms_scenario_gen 
// are the base classes provided by VMM for this functionality. This section describes 
// the various usages of multi-stream scenario generation with these base classes.
//
//  Generated scenarios can be transferred to any number of channels of various types, 
// anytime during simulation, making this solution very scalable, dynamic and completely 
// controllable. Moreoverer, it is possible to model sub-scenarios that can be attached 
// and controlled by an overall scenario, in a hierarchical way. You can determine 
// the number of scenarios or the number of transactions to be generated, either 
// on a MSS basis or on a given scenario generator, making this use model scalable 
// from block to system level.
//
//  It is also possible to add or remove scenarios as simulation advances, facilitating 
// detection of corner cases or address other constraints on the fly.
//  
// Function: get_context_gen 
// 
// Returns a reference to the multi-stream scenario generator that is providing the context
// for the execution of this multi-stream scenario descriptor. Returns NULL, if this
// multi-stream scenario descriptor is not registered with a multi-stream scenario
// generator. 
// 
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_ms_scenario;
//|      vmm_ms_scenario_gen atm_ms_gen = 
//|          new("Atm Scenario Gen", 12);
//|      vmm_ms_scenario ms_scen = new;
//|      ...
//|      initial begin
//|         atm_ms_gen.register_ms_scenario(
//|             "FIRST SCEN",first_ms_scen);
//|         ...
//|         if(my_scen.get_context_gen())
//|            vmm_log(log,"This scenario has been registered\n");
//|            ...
//|         else
//|            vmm_log(log,"Scenario not yet registered \n");
//|         ...
//|      end
//|   endprogram
function vmm_ms_scenario_gen vmm_ms_scenario::get_context_gen();
    if (this.context_scenario_gen == null) begin
       vmm_scenario p;
       vmm_ms_scenario q;

       // Inherit the context of the parent
       p = this.get_parent_scenario();
       if (p == null || !$cast(q, p)) return null;
       return q.get_context_gen();
    end
    return this.context_scenario_gen;
endfunction: get_context_gen


function string vmm_ms_scenario::psdisplay(string prefix);
   return super.psdisplay(prefix);
endfunction: psdisplay

// //////////////////////////////////////////// 
// Function: get_ms_scenario 
// 
// Returns a copy of the multi-stream scenario that is registered under the specified
// scenario name, in the multi-stream generator that is registered under the specified
// generator name. Returns NULL, if no such scenario exists. 
// If no generator name is specified, searches the scenario registry of the generator
// that is executing this scenario. 
// The scenario can then be executed within the context of the generator where it is registered
// by calling its <execute> method. 
// 
//|   
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   program test_ms_scenario;
//|      vmm_ms_scenario_gen atm_ms_gen = 
//|         new("Atm Scenario Gen", 12);
//|      vmm_ms_scenario first_ms_scen = new;
//|      vmm_ms_scenario buffer_ms_scen = new;
//|      ...
//|      initial begin
//|         atm_ms_gen.register_ms_scenario("FIRST SCEN",first_ms_scen);
//|         ...
//|         buffer_ms_scen = atm_ms_gen.get_ms_scenario("FIRST SCEN");
//|         if(buffer_ms_scen != null)
//|            vmm_log(log,"Returned scenario \n");
//|            ...
//|         else
//|            vmm_log(log,"Returned null, scenario doesn't exists\n");
//|         ...
//|      end
//|   
//|   endprogram
function vmm_ms_scenario vmm_ms_scenario::get_ms_scenario(string scenario, string gen = "");
    vmm_ms_scenario_gen g = this.get_context_gen();
    vmm_log log = this.get_vmm_log();

    if (g == null) begin
        `vmm_error(log, "User needs to register this scenario with a ms scenario generator before calling vmm_ms_scenario::get_ms_scenario()");
        return null;
    end
    if (gen == "") begin
        return g.get_ms_scenario(scenario);
    end
    else begin
        vmm_ms_scenario_gen ext_gen;
        ext_gen = g.get_ms_scenario_gen(gen);
        if (ext_gen == null) begin
           return null;
        end
        return ext_gen.get_ms_scenario(scenario);
    end
endfunction: get_ms_scenario


// //////////////////////////////////////////// 
// Function: get_channel 
// 
// Returns the output channel, which is registered under the specified logical name in
// the multi-stream generator where the multi-stream scenario generator is registered.
// Returns NULL, if no such channel exists. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm trans")
//|   
//|   program test_ms_scenario;
//|      vmm_ms_scenario_gen atm_ms_gen = 
//|         new("Atm Scenario Gen", 12);
//|      atm_cell_channel my_chan=new("MY_CHANNEL", "EXAMPLE");
//|      atm_cell_channel buffer_channel = new("MY_BUFFER", "EXAMPLE");
//|      ...
//|      initial begin
//|         ...
//|         buffer_channel = atm_ms_gen.get_channel("MY_CHANNEL");
//|         if(buffer_channel != null)
//|            vmm_log(log,"Returned channel \n");
//|            ...
//|         else
//|            vmm_log(log,"Returned null value\n");
//|         ...
//|      end
//|   
//|   endprogram
function vmm_channel vmm_ms_scenario::get_channel(string name);
    vmm_ms_scenario_gen gen = this.get_context_gen();
    vmm_log log = this.get_vmm_log();
    if (gen == null) begin
        `vmm_error(log, "User needs to register this scenario with a ms scenario generator before calling vmm_ms_scenario::get_channel()");
        return null;
    end
    return gen.get_channel(name);
endfunction: get_channel


task vmm_ms_scenario::grab_channels(ref vmm_channel channels[$]);
   bit retry;
   forever begin
      retry = 0;
      foreach (channels[i]) begin
         if (!channels[i].try_grab(this)) begin
            for (int j = 0; j < i; j++) channels[j].ungrab(this);
            channels[i].notify.wait_for(vmm_channel::UNGRABBED);
            retry = 1;
            break;
         end
      end
      if (!retry) return;
   end
endtask


function vmm_data vmm_ms_scenario::copy(vmm_data to = null);
   vmm_ms_scenario cpy;
   vmm_log log = this.get_vmm_log();

   if (to == null) begin
      if (this.context_scenario_gen != null) log = this.context_scenario_gen.log;

      `vmm_error(log, {"You need to define the vmm_ms_scenario::copy() method to implement multi-stream scenario '", this.scenario_name(), "'"});

      return null;
   end
   if (!$cast(cpy, to)) begin
      `vmm_fatal(log, "Cannot copy to non-vmm_ms_scenario instance");
      return null;
   end

   cpy.context_scenario_gen = this.context_scenario_gen;

   return super.copy(cpy);
endfunction: copy


function vmm_ms_scenario_gen::new(string inst,
                                  int stream_id = -1
                                  `VMM12_XACTOR_NEW_ARGS `VMM_XACTOR_NEW_ARGS);
    super.new("VMM Multistream Scenario Generator", inst, stream_id
              `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL);

    this.scenario_count = 0;
    this.inst_count = 0;
    this.stop_after_n_insts = 0;
    this.stop_after_n_scenarios = 0;

    this.select_scenario = new;

    void'(this.notify.configure(GENERATED));
    void'(this.notify.configure(DONE, vmm_notify::ON_OFF));
endfunction: new


function string vmm_ms_scenario_gen::psdisplay(string prefix = "");
   psdisplay = super.psdisplay(prefix);
   $sformat(psdisplay, "%s [stops after #insts %0d>%0d or #scenarios %0d>%0d]",
            psdisplay, this.inst_count, this.stop_after_n_insts,
            this.scenario_count, this.stop_after_n_scenarios);

   foreach (this.channel_registry[i]) begin
      string pfx;
      $sformat(pfx, "%s  Channel \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.channel_registry[i].psdisplay(pfx)};
   end

   foreach (this.mss_registry[i]) begin
      string pfx;
      $sformat(pfx, "%s  Scenario \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.mss_registry[i].psdisplay(pfx)};
   end

   foreach (this.mssg_registry[i]) begin
      string pfx;
      $sformat(pfx, "%s  SubGen'tor \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.mssg_registry[i].psdisplay(pfx)};
   end
   return psdisplay;
endfunction


// //////////////////////////////////////////// 
// Function: get_n_insts 
// 
// Returns the current value of the inst_count property. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario_gen;
//|      ...
//|      function void print_ms_gen_fields();
//|         ...
//|         `vmm_note(log,$psprintf(
//|            "Present instance count is %d\n", 
//|            this.get_n_insts()));
//|      endfunction
//|   endclass
//|   
//|   program test_scen;
//|      my_ms_scen my_gen= new("MY MS SCENARIO",10);
//|      initial begin
//|      my_gen.print_ms_gen_fields();
//|      end
//|   end
function int unsigned vmm_ms_scenario_gen::get_n_insts();
    get_n_insts = this.inst_count;
endfunction: get_n_insts


// //////////////////////////////////////////// 
// Function: get_n_scenarios 
// 
// Returns the current value of the scenario_count property.
// 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario_gen;
//|      ...
//|      function void print_ms_gen_fields();
//|         ...
//|         `vmm_note(log,$psprintf(
//|             "Present scenario count is %d\n",
//|             this.get_n_scenarios()));
//|      endfunction
//|   endclass
//|   
//|   program test_scen;
//|      my_ms_scen my_gen= new("MY MS SCENARIO",10);
//|      initial begin
//|      my_gen.print_ms_gen_fields();
//|      end
//|   end
function int unsigned vmm_ms_scenario_gen::get_n_scenarios();
    get_n_scenarios = this.scenario_count;
endfunction: get_n_scenarios

function void vmm_ms_scenario_gen::reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
    super.reset_xactor(rst_typ);
    this.scenario_count = 0;
    this.inst_count = 0;
    `vmm_delQ(this.select_scenario.last_selected);

    if(rst_typ >= FIRM_RST) begin
        this.notify.reset( , vmm_notify::HARD);
    end

    if(rst_typ >= HARD_RST) begin
        this.stop_after_n_insts = 0;
        this.stop_after_n_scenarios = 0;
        this.select_scenario = new;
    end
endfunction: reset_xactor

function void vmm_ms_scenario_gen::start_xactor();
`ifdef VMM12_XACTOR_BASE
    `vmm_unit_config_int(stop_after_n_scenarios, stop_after_n_scenarios, "runs number of scenarios", 0, DO_ALL)
    `vmm_unit_config_int(stop_after_n_insts, stop_after_n_insts, "runs number of instances", 0, DO_ALL)
`endif
     super.start_xactor();
endfunction: start_xactor

// //////////////////////////////////////////// 
// Function: register_channel 
// 
// Registers the specified output channel under the specified logical name. The same
// channel may be registered multiple times under different names, thus creating an alias
// to the same channel. 
// Once registered, the output channel is available under the specified logical name
// to multi-stream scenarios through the <vmm_ms_scenario::get_channel> method.
// 
// It is an error to register a channel under a name that already exists. Use the <replace_channel>
// to replace a registered scenario. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|      vmm_ms_scenario_gen my_ms_gen = 
//|         new("MS Scenario Gen", 11);
//|      atm_cell_channel ms_chan_1 = 
//|         new("MS-CHANNEL-1", "MY_CHANNEL");
//|      ...
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering channel \n");
//|         my_ms_gen.register_channel("MS-channel-1",ms_chan_1);
//|         ...
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::register_channel(string name,
                                                    vmm_channel chan);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::register_channel()");
        return;
    end
    if(this.channel_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("A channel has already been register under the name '%s'. Use vmm_ms_scenario_gen::replace_channel() instead.", name));
        return;
    end
    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null channel name specified to vmm_ms_scenario_gen::register_channel(%s)", name));
        return;
    end

    this.channel_registry[name] = chan;
endfunction: register_channel


// //////////////////////////////////////////// 
// Function: channel_exists 
// 
// Returns TRUE, if there is an output channel registered under the specified name. Otherwise,
// it returns FALSE. 
// Use the <get_channel> method to retrieve a channel under a
// specified name. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|      vmm_ms_scenario_gen my_ms_gen = 
//|         new("MS Scenario Gen", 11);
//|      atm_cell_channel ms_chan_1 = 
//|         new("MS-CHANNEL-1", "MY_CHANNEL");
//|      ...
//|      initial begin
//|         vmm_log(log,"Registering channel \n");
//|         my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|         ...
//|         if(my_ms_gen.channel_exists("MS_CHANNEL-1"))
//|            vmm_log(log,"Channel exists\n");
//|         else
//|            vmm_log(log,"Channel not yet registered\n");
//|         ...
//|      end
//|   endprogram
function bit vmm_ms_scenario_gen::channel_exists(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::channel_exists()");
        return 0;
    end
    return this.channel_registry.exists(name);
endfunction: channel_exists


// //////////////////////////////////////////// 
// Function: replace_channel 
// 
// Registers the specified output channel under the specified name, replacing the channel
// that is previously registered under that name (if any). The same channel may be registered
// multiple times under different names, thus creating an alias to the same output channel.
// 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|   	atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|   	...
//|   	initial begin
//|   		vmm_log(log,"Registering channel \n");
//|   		my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|   		my_ms_gen.register_channel("MS-CHANNEL-2",ms_chan_1);
//|   		...
//|   		vmm_log(log,"Replacing the channel \n");
//|   		my_ms_gen.replace_channel("MS-CHANNEl-1",ms_chan_1);
//|   		...
//|   	end
//|   endprogram
function void vmm_ms_scenario_gen::replace_channel(string name,
                                                   vmm_channel chan);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::replace_channel()");
        return;
    end

    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null channel specified to vmm_ms_scenario_gen::replace_channel(%s)", name));
        return;
    end

    if(!this.channel_registry.exists(name)) begin
       `vmm_error(this.log, `vmm_sformatf("Cannot replace unregistered channel '%s'. Use vmm_ms_scenario_gen::register_channel() instead.", name));
       return;
    end
       
    this.channel_registry[name]=chan;
endfunction: replace_channel


// //////////////////////////////////////////// 
// Function: get_all_channel_names 
// 
// Appends the names under which an output channel is registered. Returns the number of
// names that were added to the array. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|      atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|      string channel_name_array[$];
//|      ...
//|      initial begin
//|         `vmm_note(log,"Registering channel \n");
//|         my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|         my_ms_gen.get_all_channel_names(channel_name_array);
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::get_all_channel_names(ref string name[$]);
   string s;

    `vmm_delQ(name);
    if(this.channel_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.channel_registry.next(s));
    end
    else begin
        `vmm_warning(this.log, "There are no entries in the channel registry");
    end
endfunction: get_all_channel_names


// //////////////////////////////////////////// 
// Function: get_names_by_channel 
// 
// Appends the names under which the specified output channel is registered. Returns
// the number of names that were added to the array. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|      atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|      string channel_name_array[$];
//|      ...
//|      initial begin
//|         `vmm_note(log,"Registering channel \n");
//|         my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|         ...
//|         my_ms_gen.get_names_by_channel(ms_chan_1,channel_name_array);
//|         ...
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::get_names_by_channel(vmm_channel chan,
                                                        ref string name[$]);
    string s;

    if(chan == null) begin
        `vmm_error(this.log, "Null channel specified to vmm_ms_scenario_gen::get_names_by_channel()");
        return;
    end

    `vmm_delQ(name);
    if(this.channel_registry.first(s)) begin
        do begin
            if(this.channel_registry[s] == chan) begin
                name.push_back(s);
            end
        end while(this.channel_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "The specified channel has not been registered with this generator");
    end
endfunction: get_names_by_channel


// //////////////////////////////////////////// 
// Function: get_channel_name 
// 
// Return a name under which the specified channel is registered. Returns "", if the channel
// is not registered. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|   	atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|   	string buffer_chan_name;
//|   	initial begin
//|   		vmm_log(log,"Registering channel \n");
//|   	my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|   		buffer_chan_name =  my_ms_gen.get_channel_name(ms_chan_1);
//|   	end
//|   endprogram
function string vmm_ms_scenario_gen::get_channel_name(vmm_channel chan);
    string s[$];

    if(chan == null) begin
        `vmm_error(this.log, "Null channel specified to vmm_ms_scenario_gen::get_channel_name()");
        return "";
    end

    this.get_names_by_channel(chan, s);
    if (s.size() > 0) return s[0];

    return "";
endfunction: get_channel_name


// //////////////////////////////////////////// 
// Function: unregister_channel 
// 
// Completely unregisters the specified output channel and returns TRUE, if it exists
// in the registry. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|   	atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|   	...
//|   	initial begin
//|   		vmm_log(log,"Registering channel \n");
//|   		my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|   		...
//|   		if(my_ms_gen.unregister_channel(ms_chan_1)
//|   			vmm_log(log,"Channel has been unregistered\n");
//|   		...
//|   	end
//|   endprogram
function bit vmm_ms_scenario_gen::unregister_channel(vmm_channel chan);
    string s;

    unregister_channel = 0;

    if(chan == null) begin
        `vmm_error(this.log, "Null channel specified to vmm_ms_scenario_gen::unregister_channel()");
        return 0;
    end

    if(this.channel_registry.first(s)) begin
        do begin
            if(this.channel_registry[s] == chan) begin
                this.channel_registry.delete(s);
                unregister_channel = 1;
            end
        end while(this.channel_registry.next(s));
    end
    if(unregister_channel==0) begin
        `vmm_warning(this.log, "The channel specified to vmm_ms_scenario_gen::unregister_channel() has not been previously registered");
    end
endfunction: unregister_channel


// //////////////////////////////////////////// 
// Function: unregister_channel_by_name 
// 
// Unregisters the output channel under the specified name, and returns the unregistered
// channel. Returns NULL, if there is no channel registered under the specified name.
// 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|   	atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|   	atm_cell_channel buffer_chan = new("BUFFER","MY_BC");
//|   	...
//|   	initial begin
//|   		vmm_log(log,"Registering channel \n");
//|   		my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|   		...
//|   		vmm_log(log,"Unregistered channel by name \n");
//|   		buffer_chan = my_ms_gen.unregister_channel_by_name("MS-CHANNEL-
//|   
//|   
//|   1");
//|   		...
//|   	end
//|   endprogram
function vmm_channel vmm_ms_scenario_gen::unregister_channel_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::unregister_channel_by_name()");
        return null;
    end

    if(!this.channel_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no channel registered under the name '%s'", name));
        return null;
    end
    else begin
        unregister_channel_by_name = this.channel_registry[name];
        this.channel_registry.delete(name);
    end
endfunction: unregister_channel_by_name


// //////////////////////////////////////////// 
// Function: get_channel 
// 
// Returns the output channel registered under the specified name. Generates a warning
// message and returns NULL, if there are no channels registered under that name. 
// 
//|   
//|   `vmm_channel(atm_cell)
//|   `vmm_scenario_gen(atm_cell, "atm_trans")
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 11);
//|   	atm_cell_channel ms_chan_1=new("MS-CHANNEL-1", "MY_CHANNEL");
//|   	atm_cell_channel buffer_chan = new("BUFFER","MY_BC");
//|   	...
//|   	initial begin
//|   		vmm_log(log,"Registering channel \n");
//|   		my_ms_gen.register_channel("MS-CHANNEL-1",ms_chan_1);
//|   		...
//|   		buffer_chan = my_ms_gen.get_channel("MS-CHANNEL-1");
//|   		...
//|   	end
//|   endprogram
function vmm_channel vmm_ms_scenario_gen::get_channel(string name);
    if (name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::get_channel()");
        return null;
    end

    if(!this.channel_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("There is no channel registered under the name '%s'", name));
        return null;
    end

    get_channel = this.channel_registry[name];

    if(get_channel == null)
        `vmm_warning(this.log, `vmm_sformatf("Channel '%s' has a null channel associated with it in the channel registry", name));
endfunction: get_channel


// //////////////////////////////////////////// 
// Function: register_ms_scenario 
// 
// Registers the specified multi-stream scenario under the specified name. The same
// scenario may be registered multiple times under different names, thus creating an
// alias to the same scenario. 
// Registering a scenario implicitly appends it to the scenario set, if it is not already
// in the scenario_set[$] array. 
// It is an error to register a scenario under a name that already exists. Use the <replace_ms_scenario>
// to replace a registered scenario. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|   	...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|   	...
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS SCEN-1",ms_scen);
//|         ...
//|   	end
//|   endprogram
function void vmm_ms_scenario_gen::register_ms_scenario(string name,
                                                    vmm_ms_scenario scenario);
    int i;

    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::register_ms_scenario()");
        return;
    end

    if(this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("A multi-stream scenario is already registered under the name '%s'. Use vmm_ms_scenario_gen::replace_ms_scenario() instead.", name));
        return;
    end
    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null multi-stream scenario specified to vmm_ms_scenario_gen::register_ms_scenario(%s)", name));
        return;
    end

    // set the context generator for this scenario
    scenario.Xset_context_genX(this);
    this.mss_registry[name] = scenario;

    // add the ms_scenario to the scenario_set only
    // if this scenario was not previously added
    foreach(this.scenario_set[i]) begin
        if(this.scenario_set[i] == scenario)
            return;
    end
    this.scenario_set.push_back(scenario);
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
    `VMM_OBJECT_SET_PARENT(scenario, this)
    scenario.set_object_name(name);
`endif
`endif
endfunction: register_ms_scenario


// //////////////////////////////////////////// 
// Function: ms_scenario_exists 
// 
// Returns TRUE, if there is a multi-stream scenario registered under the specified name.
// Otherwise, it returns FALSE. 
// Use the <get_ms_scenario> method to retrieve a scenario under
// a specified name. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS SCEN-1",ms_scen);
//|         ...
//|         if(my_ms_gen.ms_scenario_exists("MS-SCEN-1"))
//|            `vmm_note(log, "Scenario MS-SCEN-1 is registered");
//|         else
//|            `vmm_note(log, 
//|               "Scenario MS-SCEN-1 is not yet registered");
//|         ...
//|      end
//|   endprogram
function bit vmm_ms_scenario_gen::ms_scenario_exists(string name);
    if (name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::ms_scenario_exists()");
        return 0;
    end

    return this.mss_registry.exists(name);
endfunction: ms_scenario_exists


// //////////////////////////////////////////// 
// Function: replace_ms_scenario 
// 
// Registers the specified multi-stream scenario under the specified name, replacing
// the scenario that is previously registered under that name (if any). The same scenario
// may be registered multiple times, under different names, thus creating an alias to
// the same scenario. 
// Registering a scenario implicitly appends it to the scenario set, if it is not already
// in the scenario_set[$] array. The replaced scenario is removed
// from the scenario_set[$] array, if it is not also registered
// under another name. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         my_ms_gen.register_ms_scenario("MS SCEN-1",ms_scen);
//|         my_ms_gen.register_ms_scenario("MS SCEN-2",ms_scen);
//|         ...
//|         vmm_log(log,"Replacing MS scenario \n");
//|         my_ms_gen.replace_ms_scenario("MS SCEN-1",ms_scen);
//|         ...
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::replace_ms_scenario(string name,
                                                       vmm_ms_scenario scenario);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::replace_ms_scenario()");
        return;
    end
    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null scenario specified to vmm_ms_scenario_gen::replace_ms_scenario(%s)", name));
        return;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("Cannot replace unregistered scenario '%s'. Use vmm_ms_scenario_gen::register_ms_scenario() instead.", name));
        return;
    end

    scenario.Xset_context_genX(this);

    // remove the scenario from the scenario_set
    foreach(this.scenario_set[i]) begin
        if(this.scenario_set[i] == this.mss_registry[name]) begin
            this.scenario_set.delete(i);
            break;
        end
    end
    this.mss_registry[name] = scenario;
    foreach(this.scenario_set[i]) begin
        if(this.scenario_set[i] == scenario)
            return;
    end
    this.scenario_set.push_back(scenario);
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
    `VMM_OBJECT_SET_PARENT(scenario, this)
    scenario.set_object_name(name);
`endif
`endif
endfunction: replace_ms_scenario


// //////////////////////////////////////////// 
// Function: get_all_ms_scenario_names 
// 
// Appends the names under which a multi-stream scenario descriptor is registered. Returns
// the number of names that were added to the array. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|   endclass
//|   program test_scenario;
//|      string scen_name_arr[$];
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      initial begin
//|         `vmm_note(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS-SCEN-1",ms_scen);
//|         my_ms_gen.register_ms_scenario("MS-SCEN-2",ms_scen);
//|       my_ms_gen.get_all_ms_scenario_names(scen_name_arr); 
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::get_all_ms_scenario_names(ref string name[$]);
    string s;

    `vmm_delQ(name);    
    if(this.mss_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.mss_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no multi-stream scenarios registered with this generator.");
    end
endfunction: get_all_ms_scenario_names


// //////////////////////////////////////////// 
// Function: get_names_by_ms_scenario 
// 
// Appends the names under which the specified multi-stream scenario descriptor is registered.
// Returns the number of names that were added to the array. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      string scen_name_arr[$];
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      ...
//|      initial begin
//|         ...
//|         `vmm_note(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS-SCEN-1",ms_scen);
//|         my_ms_gen.register_ms_scenario("MS-SCEN-2",ms_scen);
//|         ...
//|         my_ms_gen.get_names_by_ms_scenario(
//|            ms_scen,scen_name_arr);
//|         ...
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::get_names_by_ms_scenario(vmm_ms_scenario scenario,
                                                            ref string name[$]);
    string s;

    if(scenario == null) begin
        `vmm_error(this.log, "Null multi-stream scenario specified to vmm_ms_scenario_gen::get_names_by_ms_scenario()");
        return;
    end

    `vmm_delQ(name);
    if(this.mss_registry.first(s)) begin
        do begin
            if(this.mss_registry[s] == scenario)
                name.push_back(s);
        end while(this.mss_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "The specified multi-stream scenario is not registered with this generator");
    end
endfunction: get_names_by_ms_scenario


// //////////////////////////////////////////// 
// Function: get_ms_scenario_name 
// 
// Returns a name under which the specified multi-stream scenario descriptor is registered.
// Returns "", if the scenario is not registered. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      string buffer_name;
//|   
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS-SCEN-1",ms_scen);
//|         ...
//|         buffer_name = my_ms_gen.get_ms_scenario_name(ms_scen);
//|         vmm_note(log,
//|            `vmm_sformatf(
//|               "Registered name for ms_scen is: %s\n",
//|               buffer_name));
//|         ...
//|      end
//|   endprogram
function string vmm_ms_scenario_gen::get_ms_scenario_name(vmm_ms_scenario scenario);
    string s[$];

    if(scenario == null) begin
        `vmm_error(this.log, "Null multi-stream scenario specified to vmm_ms_scenario_gen::get_ms_scenario_name()");
        return "";
    end

    this.get_names_by_ms_scenario(scenario, s);
    if (s.size() > 0) return s[0];

    return "";
endfunction: get_ms_scenario_name


// //////////////////////////////////////////// 
// Function: get_ms_scenario_index 
// 
// Returns the index of the specified scenario descriptor in the scenario_set[$]
// array. A warning message is generated and returns -1, if the scenario descriptor is
// not found in the scenario set. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      int buffer_index;
//|   
//|      initial begin
//|         ...
//|         vmm_log(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS-SCEN-1",ms_scen);
//|         ...
//|         buffer_index =
//|            my_ms_gen.get_ms_scenario_index(ms_scen);
//|         vmm_note(log,`vmm_sformatf(
//|            "Index for ms_scen is : %d\n",buffer_index));
//|         ...
//|      end
//|   endprogram
function int vmm_ms_scenario_gen::get_ms_scenario_index(vmm_ms_scenario scenario);
    foreach(this.scenario_set[i]) begin
       if(this.scenario_set[i] == scenario) begin
          return i;
       end
    end

    `vmm_warning(this.log, `vmm_sformatf("The scenario specified to vmm_ms_scenario_gen::get_ms_scenario_index() cannot be found in the vmm_ms_scenario_gen::scenario_set[] array"));

    return -1;
endfunction: get_ms_scenario_index


// //////////////////////////////////////////// 
// Function: unregister_ms_scenario 
// 
// Completely unregisters the specified multi-stream scenario descriptor and returns
// TRUE, if it exists in the registry. The unregistered scenario is also removed from the
// scenario_set[$] array. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      ...
//|      initial begin
//|         my_ms_gen.register_ms_scenario("MS SCEN-1",ms_scen);
//|         ...
//|         if(my_ms_gen.unregister_ms_scenario(ms_scen)
//|            vmm_log(log,"Scenario unregistered \n");
//|         else
//|            vmm_log(log,"Unable to unregister  \n");
//|         ...
//|      end
//|   endprogram
function bit vmm_ms_scenario_gen::unregister_ms_scenario(vmm_ms_scenario scenario);
    string s;

    unregister_ms_scenario=0;

    if(scenario == null) begin
        `vmm_error(this.log, "Null scenario specified to vmm_ms_scenario_gen::unregister_ms_scenario()");
        return 0;
    end

    if(this.mss_registry.first(s)) begin
        do begin
            if(this.mss_registry[s] == scenario) begin
                this.mss_registry.delete(s);
                unregister_ms_scenario=1;
            end
        end while(this.mss_registry.next(s));
    end
    if(unregister_ms_scenario == 0) begin
       `vmm_warning(this.log, "The scenario specified to vmm_ms_scenario_gen::unregister_ms_scenario() has not been previously registered with this generator");
       return 0;
    end

    scenario.Xset_context_genX(null);
    foreach(this.scenario_set[i]) begin
       if(this.scenario_set[i] == scenario) begin
          this.scenario_set.delete(i);
          break;
       end
    end
endfunction: unregister_ms_scenario


// //////////////////////////////////////////// 
// Function: unregister_ms_scenario_by_name 
// 
// Unregisters the multi-stream scenario under the specified name, and returns the unregistered
// scenario descriptor. Returns NULL, if there is no scenario registered under the specified
// name. 
// The unregistered scenario descriptor is removed from the scenario_set[$]
// array, if it is not also registered under another name. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|      ...
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      my_ms_scen buffer_scen =new;
//|      ...
//|      initial begin
//|         my_ms_gen.register_ms_scenario("MS SCEN-1",ms_scen);
//|         ...
//|         buffer_scen = 
//|            my_ms_gen.unregister_ms_scenario_by_name(
//|               "MY-SCEN-1",ms_scen);
//|         if(buffer_scen == null)
//|            vmm_log(log,"Returned null value \n");
//|        ...
//|      end
//|   endprogram
function vmm_ms_scenario vmm_ms_scenario_gen::unregister_ms_scenario_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::unregister_ms_scenario_by_name()");
        return null;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no multi-stream scenario registered under the name '%s' with this generator", name));
        return null;
    end
    else begin
        unregister_ms_scenario_by_name = this.mss_registry[name];
        // delete it from the scenario set
        foreach(this.scenario_set[i]) begin
            if(this.scenario_set[i] == this.mss_registry[name]) begin
                this.scenario_set.delete(i);
                break;
            end
        end
        this.mss_registry.delete(name);
        unregister_ms_scenario_by_name.Xset_context_genX(null);
    end
endfunction: unregister_ms_scenario_by_name


// //////////////////////////////////////////// 
// Function: get_ms_scenario 
// 
// Returns a copy of the multi-stream scenario descriptor that is registered under the
// specified name. Generates a warning message and returns NULL, if there are no scenarios
// registered under that name. 
// 
//|   
//|   class my_ms_scen extends vmm_ms_scenario;
//|   endclass
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen my_ms_gen = new("MS Scenario Gen", 9);
//|      my_ms_scen ms_scen = new;
//|      my_ms_scen buffer_scen = new;
//|      initial begin
//|         vmm_log(log,"Registering MS scenario \n");
//|         my_ms_gen.register_ms_scenario("MS-SCEN-1",ms_scen);
//|         buffer_scen = my_ms_gen.get_ms_scenario("MY-SCEN_1");
//|      end
//|   endprogram
function vmm_ms_scenario vmm_ms_scenario_gen::get_ms_scenario(string name);
    string s = name;

    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::get_ms_scenario()");
        return null;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("There is no multi-stream scenario registered under the name '%s' in this generator", name));
        return null;
    end
    get_ms_scenario=this.mss_registry[name];

    if(get_ms_scenario == null)
        `vmm_warning(this.log, `vmm_sformatf("Scenario '%s' has a null scenario descriptor in the scenario registry", name));

    $cast(get_ms_scenario, get_ms_scenario.copy());
    if(get_ms_scenario != null) begin
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(get_ms_scenario, this)  
      get_ms_scenario.set_object_name(name);
`endif
`endif
    end
endfunction: get_ms_scenario


// //////////////////////////////////////////// 
// Function: register_ms_scenario_gen 
// 
// Registers the specified sub-generator under the specified logical name. The same
// generator may be registered multiple times under different names, therefore creating
// an alias to the same generator. 
// Once registered, the multi-stream generator becomes available under the specified
// logical name to multi-stream scenarios via the <vmm_ms_scenario::get_ms_scenario>
// method to create hierarchical multi-stream scenarios. 
// It is an error to register a generator under a name that already exists. Use the <replace_ms_scenario_gen>
// method to replace a registered generator. 
// 
//|   
//|   program test_scen;
//|   	vmm_ms_scenario_gen parent_ms_gen = new("Parent-MS-Scen-Gen", 11);
//|   	vmm_ms_scenario_gen child_ms_gen = new(" Child-MS-Scen-Gen", 6);
//|   	...
//|   	initial begin
//|   		vmm_log(log,"Registering sub MS generator \n");
//|   		parent_ms_gen.register_ms_scenario_gen("Child-MS-Scen-
//|   
//|   
//|   Gen",child_ms_gen);
//|   		...
//|   	end
//|   endprogram
function void vmm_ms_scenario_gen::register_ms_scenario_gen(string name,
                                                            vmm_ms_scenario_gen scenario_gen);

    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::register_ms_scenario_gen()");
        return;
    end

    if(this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("There is already a multi-stream scenario generator registered under the name '%s'. Use vmm_ms_scenario_gen::register_ms_scenario_gen() instead.", name));
        return;
    end

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null multi-stream scenario generator specified to vmm_ms_scenario_gen::register_ms_scenario_gen(%s)", name));
        return;
    end

    this.mssg_registry[name] = scenario_gen;
`ifdef VMM12_XACTOR_BASE
    scenario_gen.stop_xactor();
    scenario_gen.implicit_phasing(0);
`ifdef VMM_12_UNDERPIN_VMM_DATA
    `VMM_OBJECT_SET_PARENT(scenario_gen, this)
    scenario_gen.set_object_name(name);
`endif
`endif
endfunction: register_ms_scenario_gen


// //////////////////////////////////////////// 
// Function: ms_scenario_gen_exists 
// 
// Returns TRUE, if there is a sub-generator registered under the specified name. Otherwise,
// it returns FALSE. 
// Use the <get_ms_scenario_gen> to retrieve a sub-generator
// under a specified name. 
// 
//|   
//|   program test_scen;
//|      vmm_ms_scenario_gen parent_ms_gen = 
//|         new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen = 
//|         new(" Child-MS-Scen-Gen", 6);
//|      ...
//|      initial begin
//|         vmm_log(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Scen-Gen",child_ms_gen);
//|         ...
//|         if(parent_ms_gen.ms_scenario_gen_exists(
//|               "Child-MS-Scen-Gen"))
//|            `vmm_note(log, "Generator exists in registry");
//|         else
//|            `vmm_note(log, 
//|                "Generator doesn't exist in registry");
//|         ...
//|      end
//|   endprogram
function bit vmm_ms_scenario_gen::ms_scenario_gen_exists(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::ms_scenario_gen_exists()");
        return 0;
    end

   return this.mssg_registry.exists(name);
endfunction: ms_scenario_gen_exists


// //////////////////////////////////////////// 
// Function: replace_ms_scenario_gen 
// 
// Registers the specified sub-generator under the specified name, replacing the generator
// that is previously registered under that name (if any). The same generator may be registered
// multiple times under different names, thus creating an alias to the same sub-generator.
// 
// 
function void vmm_ms_scenario_gen::replace_ms_scenario_gen(string name,
                                                           vmm_ms_scenario_gen scenario_gen);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::replace_ms_scenario_gen()");
        return;
    end

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("Null multi-stream scenario generator specified to vmm_ms_scenario_gen::replace_ms_scenario_gen(%s)", name));
        return;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("There is no multi-stream scenario generator previsouly registered under the name '%s'. Use vmm_ms_scenario_gen::register_ms_scenario_gen() instead", name));
        return;
    end

`ifdef VMM12_XACTOR_BASE
    this.mssg_registry[name].implicit_phasing(1);
`endif
    this.mssg_registry[name] = scenario_gen;
`ifdef VMM12_XACTOR_BASE
    `VMM_OBJECT_SET_PARENT(scenario_gen, this)
    scenario_gen.set_object_name(name);
    scenario_gen.stop_xactor();
    scenario_gen.implicit_phasing(0);
`endif
endfunction: replace_ms_scenario_gen


// //////////////////////////////////////////// 
// Function: get_all_ms_scenario_gen_names 
// 
// Appends the names under which a sub-generator is registered. Returns the number of
// names that were added to the array. 
// 
//|   
//|   program test_scenario;
//|      string ms_gen_names_arr[$];
//|      vmm_ms_scenario_gen parent_ms_gen = 
//|         new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen  = 
//|         new("Child-MS-Scen-Gen", 6);
//|      ...
//|      initial begin
//|         `vmm_note(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Scen-Gen",child_ms_gen);
//|         parent_ms_gen.get_all_ms_scenario_gen_names(
//|            ms_gen_names_arr);
//|      end
//|   endprogram
function void vmm_ms_scenario_gen::get_all_ms_scenario_gen_names(ref string name[$]);
    string s;

    `vmm_delQ(name);
    if(this.mssg_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.mssg_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no multi-stream scenario generators registeres with this generator");
    end
endfunction: get_all_ms_scenario_gen_names


// //////////////////////////////////////////// 
// Function: get_names_by_ms_scenario_gen 
// 
// Appends the names under which the specified sub-generator is registered. Returns
// the number of names that were added to the array. 
// 
//|   
//|   program test_scenario;
//|      string ms_gen_names_arr[$];
//|      vmm_ms_scenario_gen parent_ms_gen =
//|          new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen  = 
//|          new("Child-MS-Scen-Gen", 6);
//|      ...
//|      initial begin
//|         `vmm_note(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Scen-Gen", child_ms_gen);
//|         ...
//|         parent_ms_gen.get_names_by_ms_scenario_gen(child_ms_gen,  
//|        ms_gen_names_arr);
//|         ...
//|      end
//|   
//|   endprogram
function void vmm_ms_scenario_gen::get_names_by_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen,
                                                                ref string name[$]);
    string s;

    if(scenario_gen == null) begin
        `vmm_error(this.log, "Null multi-stream scenario generator specified to vmm_ms_scenario_gen::get_names_by_ms_scenario_gen()");
        return;
    end

    `vmm_delQ(name);
    if(this.mssg_registry.first(s)) begin
        do begin
            if(this.mssg_registry[s] == scenario_gen)
                name.push_back(s);
        end while(this.mssg_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "The specified multi-stream scenario generator is not registered with this multi-stream scenario generator");
    end
endfunction: get_names_by_ms_scenario_gen


// //////////////////////////////////////////// 
// Function: get_ms_scenario_gen_name 
// 
// Returns a name under which the specified sub-generator is registered. Returns "",
// if the generator is not registered. 
// 
//|   
//|   program test_scenario;
//|      string buffer_ms_gen_name;
//|      vmm_ms_scenario_gen parent_ms_gen = 
//|         new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen  = 
//|         new("Child-MS-Scen-Gen", 6);
//|      initial begin
//|         vmm_log(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Scen-Gen",child_ms_gen);
//|         buffer_ms_gen_name = 
//|            parent_ms_gen.get_ms_scenario_gen_name(
//|            child_ms_gen);
//|      end
//|   endprogram
function string vmm_ms_scenario_gen::get_ms_scenario_gen_name(vmm_ms_scenario_gen scenario_gen);
    string s[$];

    if(scenario_gen == null) begin
        `vmm_error(this.log, "Null multi-stream scenario generator specified to vmm_ms_scenario_gen::get_ms_scenario_gen_name()");
        return "";
    end

    this.get_names_by_ms_scenario_gen(scenario_gen, s);

    if (s.size() > 0) return s[0];

    return "";
endfunction: get_ms_scenario_gen_name


// //////////////////////////////////////////// 
// Function: unregister_ms_scenario_gen 
// 
// Completely unregisters the specified sub-generator and returns TRUE, if it exists
// in the registry. 
// 
//|   
//|   program test_scenario;
//|      string buffer_ms_gen_name;
//|      vmm_ms_scenario_gen parent_ms_gen = 
//|         new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen  = 
//|         new("Child-MS-Scen-Gen", 6);
//|      ...
//|      initial begin
//|         vmm_log(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Gen-1",child_ms_gen);
//|         ...
//|         if(parent_ms_gen.unregister_ms_scenario_gen(
//|            child_ms_gen))
//|            vmm_log(log,"Scenario unregistered \n");
//|         else
//|            vmm_log(log,"Unable to unregister  \n");
//|      end
//|   
//|   endprogram
function bit vmm_ms_scenario_gen::unregister_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen);
    string s;

    unregister_ms_scenario_gen=0;

    if(scenario_gen == null) begin
        `vmm_error(this.log, "Null multi-stream scenario generator specified to vmm_ms_scenario_gen::unregister_ms_scenario_gen()");
        return 0;
    end

    if(this.mssg_registry.first(s)) begin
        do begin
            if(this.mssg_registry[s] == scenario_gen) begin
`ifdef VMM12_XACTOR_BASE
                this.mssg_registry[s].implicit_phasing(1);
`endif
                this.mssg_registry.delete(s);
                unregister_ms_scenario_gen=1;
            end
        end while(this.mssg_registry.next(s));
    end
    if(unregister_ms_scenario_gen==0) begin
        `vmm_warning(this.log, "The specified multi-stream scenario generator is not registered with this generator");
    end
endfunction: unregister_ms_scenario_gen


function vmm_ms_scenario_gen vmm_ms_scenario_gen::unregister_ms_scenario_gen_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::unregister_ms_scenario_gen_by_name()");
        return null;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no multi-stream scenario generator registered under the name '%s' in this generator", name));
        return null;
    end
    else begin
        unregister_ms_scenario_gen_by_name = this.mssg_registry[name];
        this.mssg_registry.delete(name);
    end
endfunction: unregister_ms_scenario_gen_by_name


// //////////////////////////////////////////// 
// Function: get_ms_scenario_gen 
// 
// Returns the sub-generator that is registered under the specified name. Generates
// a warning message and returns NULL, if there are no generators registered under that
// name. 
// 
//|   
//|   program test_scenario;
//|      vmm_ms_scenario_gen parent_ms_gen = 
//|         new("Parent-MS-Scen-Gen", 11);
//|      vmm_ms_scenario_gen child_ms_gen  = 
//|         new("Child-MS-Scen-Gen", 6);
//|      vmm_ms_scenario_gen buffer_ms_gen = 
//|         new("Buffer-MS-Scen-Gen", 6);
//|      ...
//|      initial begin
//|         vmm_log(log,"Registering sub MS generator \n");
//|         parent_ms_gen.register_ms_scenario_gen(
//|            "Child-MS-Scen-Gen", child_ms_gen);
//|         ...
//|         buffer_ms_gen = parent_ms_gen.get_ms_scenario_gen( 
//|         "Child-MS-Scen-Gen");
//|      ...
//|      end
//|   endprogram
function vmm_ms_scenario_gen vmm_ms_scenario_gen::get_ms_scenario_gen(string name);
    if(name == "") begin
        `vmm_error(this.log, "No name specified to vmm_ms_scenario_gen::get_ms_scenario_gen()");
        return null;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("There is no multi-stream scenario generator registered under the name '%s' in this generator", name));
        return null;
    end
    get_ms_scenario_gen = this.mssg_registry[name];
    if(get_ms_scenario_gen == null)
        `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario generator associated with it in the multisteam scenario generator registry", name));
endfunction: get_ms_scenario_gen


task vmm_ms_scenario_gen::main();
    vmm_ms_scenario the_scenario;
    int n_insts;
    bit dropped;

    fork
        super.main();
    join_none

    if(this.scenario_set.size() == 0) begin
        // do not start the main routine
        return;
    end

    while( (this.stop_after_n_insts <=0 || this.inst_count < this.stop_after_n_insts)
           && (this.stop_after_n_scenarios <= 0 || this.scenario_count < this.stop_after_n_scenarios)) begin
        this.wait_if_stopped();

        this.select_scenario.stream_id = this.stream_id;
        this.select_scenario.scenario_id = this.scenario_count;
        this.select_scenario.n_scenarios = this.scenario_set.size();
        this.select_scenario.scenario_set = this.scenario_set;
        if(this.select_scenario.last_selected.size() == 0)
            this.select_scenario.next_in_set = 0;
        else
            this.select_scenario.next_in_set = ((this.select_scenario.last_selected[$] + 1) % this.scenario_set.size());
        if(!this.select_scenario.randomize()) begin
            `vmm_fatal(this.log, "Cannot select multistream scenario descriptor");
            continue;
        end

        if(this.select_scenario.select < 0 ||
           this.select_scenario.select >= this.scenario_set.size()) begin
            `vmm_fatal(this.log, `vmm_sformatf("Select scenario #%0d is not within available set (0-%0d)",
                                               this.select_scenario.select, this.scenario_set.size()-1));
            continue;
        end

        this.select_scenario.last_selected.push_back(this.select_scenario.select);
        while(this.select_scenario.last_selected.size() > 10) begin
            void'(this.select_scenario.last_selected.pop_front());
        end

        the_scenario = this.scenario_set[this.select_scenario.select];
        if(the_scenario == null) begin
            `vmm_fatal(this.log, `vmm_sformatf("Selected scenario #%0d does not exist",
                                               this.select_scenario.select));
            continue;
        end

        the_scenario.stream_id = this.stream_id;
        the_scenario.scenario_id = this.scenario_count;

        `vmm_callback(vmm_ms_scenario_gen_callbacks, pre_scenario_randomize(this, the_scenario));
        if(the_scenario == null) continue;

        if(!the_scenario.randomize()) begin
            `vmm_fatal(this.log, `vmm_sformatf("Cannot randomize scenario descriptor #%0d",
                                               this.select_scenario.select));
            continue;
        end

        this.scenario_count++;
        this.notify.indicate(GENERATED, the_scenario);
        n_insts=0;
        the_scenario.execute(n_insts);
        this.inst_count += n_insts;
        `vmm_callback(vmm_ms_scenario_gen_callbacks, post_scenario_gen(this, the_scenario, dropped));
    end

    this.notify.indicate(DONE);
    this.notify.indicate(XACTOR_STOPPED);
    this.notify.indicate(XACTOR_IDLE);
    this.notify.reset(XACTOR_BUSY);
endtask: main
