// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2009 Mentor Graphics Corporation
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
// This file was modified by Mentor Graphics. See QUESTA.html
// in root directory for details.


function vmm_ms_scenario::new(`VMM_SCENARIO parent = null
                                  `VMM_SCENARIO_NEW_ARGS);
    super.new(this.log `VMM_SCENARIO_NEW_CALL);
    if(this.log == null) begin
        this.log = new("Multi Stream Scenario", "Class");
        this.notify.log = this.log;
    end
    this.set_parent_scenario(parent);
endfunction: new


task vmm_ms_scenario::execute(ref int n);
    `vmm_error(this.log, "User needs to define the 'execute' for their multi stream scenarios");
endtask: execute


/*local*/ function void vmm_ms_scenario::Xset_context_genX(vmm_ms_scenario_gen gen);
    this.context_scenario_gen = gen;
endfunction: Xset_context_genX


/*local*/ function vmm_ms_scenario_gen vmm_ms_scenario::Xget_context_genX();
    Xget_context_genX = this.context_scenario_gen;
endfunction: Xget_context_genX


function string vmm_ms_scenario::psdisplay(string prefix="");
   return super.psdisplay(prefix);
endfunction: psdisplay


function vmm_ms_scenario vmm_ms_scenario::get_ms_scenario(string scenario, string gen = "");
    if(this.context_scenario_gen == null) begin
        `vmm_error(this.log, "User needs to set the context ms scenario generator for this scenario");
        return null;
    end
    if(gen == "") begin
        return this.context_scenario_gen.get_ms_scenario(scenario);
    end
    else begin
        vmm_ms_scenario_gen ext_gen;
        ext_gen=this.context_scenario_gen.get_ms_scenario_gen(gen);
        if(ext_gen == null) begin
            `vmm_error(this.log, `vmm_sformatf("Got a null handle for scenario generator %s", gen));
            return null;
        end
        return ext_gen.get_ms_scenario(scenario);
    end
endfunction: get_ms_scenario


function vmm_channel vmm_ms_scenario::get_channel(string name);
    if(this.context_scenario_gen == null) begin
        `vmm_error(this.log, "User needs to set the context ms scenario generator for this scenario");
        return null;
    end
    return this.context_scenario_gen.get_channel(name);
endfunction: get_channel


task vmm_ms_scenario::grab_channels(ref vmm_channel channels[$]);
   forever begin: retry_all
      `foreach (channels,i) begin
         if (!channels[i].try_grab(this)) begin
            for (int j = 0; j < i; j++) channels[j].ungrab(this);
            channels[i].notify.wait_for(vmm_channel::UNGRABBED);
`ifndef INCA
            disable retry_all;
`else
            i = channels.size();
`endif
         end
      end
      return;
   end
endtask


function vmm_ms_scenario_gen::new(string inst,
                                  int stream_id = -1
                                  `VMM_XACTOR_NEW_ARGS);
    super.new("VMM Multistream Scenario Generator", inst, stream_id
              `VMM_XACTOR_NEW_CALL);

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

   `foreach_aa (this.channel_registry,string,i) begin
      string pfx;
      $sformat(pfx, "%s  Channel \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.channel_registry[i].psdisplay(pfx)};
   end `foreach_aa_end (this.channel_registry,i)

   `foreach_aa (this.mss_registry,string,i) begin
      string pfx;
      $sformat(pfx, "%s  Scenario \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.mss_registry[i].psdisplay(pfx)};
   end `foreach_aa_end (this.mss_registry,i)

   `foreach_aa (this.mssg_registry,string,i) begin
      string pfx;
      $sformat(pfx, "%s  SubGen'tor \"%s\": ", prefix, i);
      psdisplay = {psdisplay, "\n", this.mssg_registry[i].psdisplay(pfx)};
   end `foreach_aa_end (this.mssg_registry,i)
   return psdisplay;
endfunction


function int unsigned vmm_ms_scenario_gen::get_n_insts();
    get_n_insts = this.inst_count;
endfunction: get_n_insts


function int unsigned vmm_ms_scenario_gen::get_n_scenarios();
    get_n_scenarios = this.scenario_count;
endfunction: get_n_scenarios


function void vmm_ms_scenario_gen::reset_xactor(vmm_xactor::reset_e rst_typ = SOFT_RST);
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


function void vmm_ms_scenario_gen::register_channel(string name,
                                                    vmm_channel chan);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end
    if(this.channel_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the channel registry", name));
        return;
    end
    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("channel passed for %s is a null value", name));
        return;
    end

    this.channel_registry[name] = chan;
endfunction: register_channel


function bit vmm_ms_scenario_gen::channel_exists(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return 0;
    end
    return this.channel_registry.exists(name);
endfunction: channel_exists


function void vmm_ms_scenario_gen::replace_channel(string name,
                                                   vmm_channel chan);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end

    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("channel passed for %s is a null value", name));
        return;
    end

    if(!this.channel_registry.exists(name)) begin
       `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_channel]", name));
       return;
    end
       
    this.channel_registry[name]=chan;
endfunction: replace_channel


function void vmm_ms_scenario_gen::get_all_channel_names(ref string name[$]);
   string s;

    if(this.channel_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.channel_registry.next(s));
    end
    else begin
        `vmm_warning(this.log, "There are no entries in the channel registry");
    end
endfunction: get_all_channel_names


function void vmm_ms_scenario_gen::get_names_by_channel(vmm_channel chan,
                                                        ref string name[$]);
    string s;

    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("channel passed is a null value"));
        return;
    end

    if(this.channel_registry.first(s)) begin
        do begin
            if(this.channel_registry[s] == chan) begin
                name.push_back(s);
            end
        end while(this.channel_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no entries in the channel registry");
    end
endfunction: get_names_by_channel


function string vmm_ms_scenario_gen::get_channel_name(vmm_channel chan);
    string s[$];

    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("channel passed is a null value"));
        return "";
    end

    this.get_names_by_channel(chan, s);
    if (s.size() > 0) return s[0];

    return "";
endfunction: get_channel_name


function bit vmm_ms_scenario_gen::unregister_channel(vmm_channel chan);
    string s;

    unregister_channel = 0;

    if(chan == null) begin
        `vmm_error(this.log, `vmm_sformatf("channel passed is a null value"));
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
        `vmm_warning(this.log, "There are no entries in the channel registry");
    end
endfunction: unregister_channel


function vmm_channel vmm_ms_scenario_gen::unregister_channel_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.channel_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the channel registry", name));
        return null;
    end
    else begin
        unregister_channel_by_name = this.channel_registry[name];
        this.channel_registry.delete(name);
    end
endfunction: unregister_channel_by_name


function vmm_channel vmm_ms_scenario_gen::get_channel(string name);
    if (name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.channel_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the channel registry", name));
        return null;
    end

    get_channel = this.channel_registry[name];

    // If null, issue a warning
    if(get_channel == null)
        `vmm_warning(this.log, `vmm_sformatf("%s has a null channel associated with it in the channel registry", name));
endfunction: get_channel


function void vmm_ms_scenario_gen::register_ms_scenario(string name,
                                                    vmm_ms_scenario scenario);
    int i;

    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end

    if(this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the multistream scenario registry", name));
        return;
    end
    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name));
        return;
    end

    // set the context generator for this scenario
    scenario.Xset_context_genX(this);
    this.mss_registry[name] = scenario;

    // add the ms_scenario to the scenario_set only
    // if this scenario was not previously added
    `foreach(this.scenario_set,i) begin
        if(this.scenario_set[i] == scenario)
            return;
    end
    this.scenario_set.push_back(scenario);
endfunction: register_ms_scenario


function bit vmm_ms_scenario_gen::ms_scenario_exists(string name);
    if (name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return 0;
    end

    return this.mss_registry.exists(name);
endfunction: ms_scenario_exists


function void vmm_ms_scenario_gen::replace_ms_scenario(string name,
                                                   vmm_ms_scenario scenario);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end
    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("scenario passed for %s is a null value", name));
        return;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_ms_scenario]", name));
        return;
    end

    scenario.Xset_context_genX(this);

    // remove the scenario from the scenario_set
    `foreach(this.scenario_set,i) begin
        if(this.scenario_set[i] == this.mss_registry[name]) begin
            this.scenario_set.delete(i);
            break;
        end
    end
    this.mss_registry[name] = scenario;
    `foreach(this.scenario_set,i) begin
        if(this.scenario_set[i] == scenario)
            return;
    end
    this.scenario_set.push_back(scenario);
endfunction: replace_ms_scenario


function void vmm_ms_scenario_gen::get_all_ms_scenario_names(ref string name[$]);
    string s;

    if(this.mss_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.channel_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no entries in the multistream scenario registry");
    end
endfunction: get_all_ms_scenario_names


function void vmm_ms_scenario_gen::get_names_by_ms_scenario(vmm_ms_scenario scenario,
                                                            ref string name[$]);
    string s;

    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("scenario passed is a null value"));
        return;
    end

    if(this.mss_registry.first(s)) begin
        do begin
            if(this.mss_registry[s] == scenario)
                name.push_back(s);
        end while(this.mss_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no entries in the multistream scenario registry");
    end
endfunction: get_names_by_ms_scenario


function string vmm_ms_scenario_gen::get_ms_scenario_name(vmm_ms_scenario scenario);
    string s[$];

    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("scenario passed is a null value"));
        return "";
    end

    this.get_names_by_ms_scenario(scenario, s);
    if (s.size() > 0) return s[0];

    return "";
endfunction: get_ms_scenario_name


function int vmm_ms_scenario_gen::get_ms_scenario_index(vmm_ms_scenario scenario);
    get_ms_scenario_index = -1;
    `foreach(this.scenario_set,i) begin
        if(this.scenario_set[i] == scenario) begin
            return i;
        end
    end
    if(get_ms_scenario_index == -1) begin
        `vmm_warning(this.log, `vmm_sformatf("Cannot find the index for the ms scenario"));
    end
endfunction: get_ms_scenario_index


function bit vmm_ms_scenario_gen::unregister_ms_scenario(vmm_ms_scenario scenario);
    string s;

    unregister_ms_scenario=0;

    if(scenario == null) begin
        `vmm_error(this.log, `vmm_sformatf("scenario passed is a null value"));
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
        `vmm_warning(this.log, "There are no entries in the multistream scenario registry");
    end
    if(unregister_ms_scenario) begin
        `foreach(this.scenario_set,i) begin
            if(this.scenario_set[i] == scenario) begin
                this.scenario_set.delete(i);
                break;
            end
        end
    end
endfunction: unregister_ms_scenario


function vmm_ms_scenario vmm_ms_scenario_gen::unregister_ms_scenario_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the multistream scenario registry", name));
        return null;
    end
    else begin
        unregister_ms_scenario_by_name = this.mss_registry[name];
        // delete it from the scenario set
        `foreach(this.scenario_set,i) begin
            if(this.scenario_set[i] == this.mss_registry[name]) begin
                this.scenario_set.delete(i);
                break;
            end
        end
        this.mss_registry.delete(name);
    end
endfunction: unregister_ms_scenario_by_name


function vmm_ms_scenario vmm_ms_scenario_gen::get_ms_scenario(string name);
    string s = name;

    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.mss_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the multistream scenario registry", name));
        return null;
    end
    get_ms_scenario=this.mss_registry[name];

    if(get_ms_scenario == null)
        `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario associated with it in the multistream scenario registry", name));
endfunction: get_ms_scenario


function void vmm_ms_scenario_gen::register_ms_scenario_gen(string name,
                                                            vmm_ms_scenario_gen scenario_gen);

    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end

    if(this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s already has an entry in the multistream scenario generator registry", name));
        return;
    end

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("multistream scenario generator for %s is a null value", name));
        return;
    end

    this.mssg_registry[name] = scenario_gen;
endfunction: register_ms_scenario_gen


function bit vmm_ms_scenario_gen::ms_scenario_gen_exists(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return 0;
    end

   return this.mssg_registry.exists(name);
endfunction: ms_scenario_gen_exists


function void vmm_ms_scenario_gen::replace_ms_scenario_gen(string name,
                                                           vmm_ms_scenario_gen scenario_gen);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return;
    end

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("multistream scenario generator for %s is a null value", name));
        return;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("cannot replace a unregistered %s entry [use register_ms_scenario_gen]", name));
        return;
    end

    this.mssg_registry[name] = scenario_gen;
endfunction: replace_ms_scenario_gen


function void vmm_ms_scenario_gen::get_all_ms_scenario_gen_names(ref string name[$]);
    string s;

    if(this.mssg_registry.first(s)) begin
        do begin
            name.push_back(s);
        end while(this.mssg_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no entries in the multistream scenario generator registry");
    end
endfunction: get_all_ms_scenario_gen_names


function void vmm_ms_scenario_gen::get_names_by_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen,
                                                                ref string name[$]);
    string s;

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("multistream scenario generator is a null value"));
        return;
    end

    if(this.mssg_registry.first(s)) begin
        do begin
            if(this.mssg_registry[s] == scenario_gen)
                name.push_back(s);
        end while(this.mssg_registry.next(s));
    end
    if(name.size() == 0) begin
        `vmm_warning(this.log, "There are no entries in the multistream scenario generator registry");
    end
endfunction: get_names_by_ms_scenario_gen


function string vmm_ms_scenario_gen::get_ms_scenario_gen_name(vmm_ms_scenario_gen scenario_gen);
    string s[$];

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("multistream scenario generator is a null value"));
        return "";
    end

    this.get_names_by_ms_scenario_gen(scenario_gen, s);

    if (s.size() > 0) return s[0];

    return "";
endfunction: get_ms_scenario_gen_name


function bit vmm_ms_scenario_gen::unregister_ms_scenario_gen(vmm_ms_scenario_gen scenario_gen);
    string s;

    unregister_ms_scenario_gen=0;

    if(scenario_gen == null) begin
        `vmm_error(this.log, `vmm_sformatf("multistream scenario generator is a null value"));
        return 0;
    end

    if(this.mssg_registry.first(s)) begin
        do begin
            if(this.mssg_registry[s] == scenario_gen) begin
                this.mssg_registry.delete(s);
                unregister_ms_scenario_gen=1;
            end
        end while(this.mssg_registry.next(s));
    end
    if(unregister_ms_scenario_gen==0) begin
        `vmm_warning(this.log, "There are no entries in the multistream scenario generator registry");
    end
endfunction: unregister_ms_scenario_gen


function vmm_ms_scenario_gen vmm_ms_scenario_gen::unregister_ms_scenario_gen_by_name(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_warning(this.log, `vmm_sformatf("There is no entry for %s in the multistream scenario generator registry", name));
        return null;
    end
    else begin
        unregister_ms_scenario_gen_by_name = this.mssg_registry[name];
        this.mssg_registry.delete(name);
    end
endfunction: unregister_ms_scenario_gen_by_name


function vmm_ms_scenario_gen vmm_ms_scenario_gen::get_ms_scenario_gen(string name);
    if(name == "") begin
        `vmm_error(this.log, `vmm_sformatf("Invalid '%s' string was passed", name));
        return null;
    end

    if(!this.mssg_registry.exists(name)) begin
        `vmm_error(this.log, `vmm_sformatf("%s does not have an entry in the multistream scenario generator registry", name));
        return null;
    end
    get_ms_scenario_gen = this.mssg_registry[name];
    if(get_ms_scenario_gen == null)
        `vmm_warning(this.log, `vmm_sformatf("%s has a null scenario generator associated with it in the multisteam scenario generator registry", name));
endfunction: get_ms_scenario_gen


task vmm_ms_scenario_gen::main();
    vmm_ms_scenario the_scenario;
    //int n_insts;

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
    end

    this.notify.indicate(DONE);
    this.notify.indicate(XACTOR_STOPPED);
    this.notify.indicate(XACTOR_IDLE);
    this.notify.reset(XACTOR_BUSY);
endtask: main
