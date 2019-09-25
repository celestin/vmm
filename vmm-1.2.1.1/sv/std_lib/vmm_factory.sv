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

//------------------------------------------------------------
// vmm_factory
//
//`ifndef NO_VMM12_PARAM_CHANNEL
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_factory_base_pattern_info;
   typedef enum {CREATE_NEW, CREATE_COPY} fact_type_e;
endclass

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_factory_pattern_info#(type T = vmm_object) extends vmm_factory_base_pattern_info;
   fact_type_e     fact_type;
   string name;
   T               factory;
   `vmm_path_regexp regexp;
   string fname;
   int lineno;

   function new(string name, T factory, fact_type_e fact_type, 
                string fname="", int lineno=0);
      this.name      = name;
      this.fact_type = fact_type;
      this.factory   = factory;
      this.fname     = fname;
      this.lineno    = lineno;
   endfunction

   function void check_n_replace_gen_factory(vmm_log log);
      vmm_ss_scenario_base scn;
      vmm_ms_scenario      ms_scn;
      vmm_data     tr;
      vmm_scenario_gen_base gen;
      vmm_ms_scenario_gen   ms_gen;
      if ($cast(scn, factory) || $cast(ms_scn, factory)) begin //factory is of vmm_ss_scenario or vmm_ms_scneario type
         vmm_object obj;
         string ghier, sname, gname, hier;
         split_hiername(name, sname, ghier);
`ifdef VMM_12_UNDERPIN_VMM_XACTOR
         obj = vmm_object::find_object_by_name(ghier); //checking if generator instance exists
         if (obj == null) `vmm_trace(log,`vmm_sformatf("the scenario '%s' doesn't exist at hierarchy %s",sname,ghier));
         else  begin //generator instance exists
            if (!$cast(gen, obj) && !$cast(ms_gen, obj)) return;
            else if ($cast(gen,obj)) check_n_add_scenario(gen, sname, scn);
            else if ($cast(ms_gen,obj)) check_n_add_ms_scenario(ms_gen, sname, ms_scn);
       
         end
         return;
`endif
         split_hiername(ghier, gname, hier);
         obj = vmm_object::find_object_by_name(hier);
         if (obj == null)begin
            `vmm_trace(log,`vmm_sformatf("the generator instance %s at hierarchy %s doesn't exist",gname,ghier));
            return; //vmm_object hierarchy doesnt exist
         end
         begin //do proper checking in case of underpinned
            `foreach_vmm_xactor(vmm_scenario_gen_base, "/./", "/./") begin
               if (xact.get_instance() != gname) continue;
               check_n_add_scenario(xact, sname, scn);
               `vmm_trace(log,`vmm_sformatf("the factory instance of the vmm scenario generator  instance '%s' at  %s will be replaced through the factory override scenario ", gname,ghier));
            end
         end
         begin //do proper checking in case of underpinned
            `foreach_vmm_xactor(vmm_ms_scenario_gen, "/./", "/./") begin
               if (xact.get_instance() != gname) continue; 
               check_n_add_ms_scenario(xact, sname, ms_scn);
               `vmm_trace(log,`vmm_sformatf("the factory instance %s of the vmm ms scenario generator  instance '%s' at  %s will be replaced through the factory override scenario ", sname, gname,ghier));
            end
         end
      end
      else if ($cast(tr, factory)) begin //factory is of vmm_data type
         string gname, ghier, trname, hier;
         vmm_object obj;
         ghier = name;
         if (`vmm_str_match(name, ":items[/(.*)/]$")) begin //scenario gen
            vmm_scenario_gen_base sgen;
            string shier, sname, str, str_idx;
            str_idx = `vmm_str_backref(name, 0);
            split_hiername(name, str, shier);
            split_hiername(shier, sname, ghier);
`ifdef VMM_12_UNDERPIN_VMM_XACTOR
            begin
               string pat = vmm_path_match::compile_pattern(ghier, log);
               `vmm_path_compiled comp_path;
               `foreach_vmm_xactor(vmm_scenario_gen_base, "/./", "/./") begin
                  if (!$cast(obj, xact)) continue;
                  comp_path = vmm_path_match::compile_path(log, null, obj.get_object_hiername());
                  if (!vmm_path_match::match(comp_path, pat)) continue; 
                  set_scn_items(sname, xact, str_idx, tr);
               end
            end
            return;
`else
            split_hiername(ghier, gname, hier);
            obj = vmm_object::find_object_by_name(hier);
            if (obj == null) return; //vmm_object hierarchy doesnt exist
            begin
              int num;
              `foreach_vmm_xactor(vmm_scenario_gen_base, "/./", "/./") begin
                 if (xact.get_instance() != gname) continue;
                 set_scn_items(sname, xact, str_idx, tr);
                 num++;
               end  
               if (num > 1) begin
                 `vmm_warning(log, `vmm_sformatf("vmm_xactor is not underpinned, factory replacement happened for items of %0d generators(%s)", num, gname));
               end
            end  
            return;
`endif
         end
         else begin
            vmm_atomic_gen_base agen;
            if (`vmm_str_match(name, ":randomized_obj$")) begin //atomic gen
               string str;
               split_hiername(name, str, ghier);
            end
`ifdef VMM_12_UNDERPIN_VMM_XACTOR
            begin
               string pat = vmm_path_match::compile_pattern(ghier, log);
               `vmm_path_compiled comp_path;
               `foreach_vmm_xactor(vmm_atomic_gen_base, "/./", "/./") begin
                  if (!$cast(obj, xact)) continue;
                  comp_path = vmm_path_match::compile_path(log, null, obj.get_object_hiername());
                  if (!vmm_path_match::match(comp_path, pat)) continue; 
                  if (fact_type == CREATE_COPY)  xact.Xset_blueprintX(tr.copy()); 
                  else xact.Xset_blueprintX(tr.allocate());
               end
            end
            return;
`else
            split_hiername(ghier, gname, hier);
            obj = vmm_object::find_object_by_name(hier);
            if (obj == null) return; //vmm_object hierarchy doesnt exist
            begin 
               int num;
               `foreach_vmm_xactor(vmm_atomic_gen_base, "/./", "/./") begin
                  if (xact.get_instance() != gname) continue;
                  if (fact_type == CREATE_COPY)  xact.Xset_blueprintX(tr.copy()); 
                  else xact.Xset_blueprintX(tr.allocate());
                  num++;
               end
               if (num > 1) begin
                 `vmm_warning(log, `vmm_sformatf("vmm_xactor is not underpinned, factory replacement happened for randomized_obj of %0d generators(%s)", num, gname));
               end
            end
`endif
         end
      end
   endfunction

   local function void check_n_add_scenario(vmm_scenario_gen_base gen,
                                            string sname, 
                                            vmm_ss_scenario_base scn);
      if (gen.scenario_exists(sname)) begin
         gen.replace_scenario(sname, scn);
      end
      else begin
         gen.register_scenario(sname, scn);
      end
   endfunction

   local function void check_n_add_ms_scenario(vmm_ms_scenario_gen gen,
                                            string sname, 
                                            vmm_ms_scenario scn);
      if (gen.ms_scenario_exists(sname)) begin
         gen.replace_ms_scenario(sname, scn);
      end
      else begin
         gen.register_ms_scenario(sname, scn);
      end
   endfunction

   local function vmm_ss_scenario_base get_scenario_by_name(string sname, 
                                                            vmm_scenario_gen_base gen);
      if (gen.scenario_exists(sname)) begin
         return gen.Xget_scenarioX(sname);
      end
   endfunction

   local function void set_scn_items(string sname, 
                                     vmm_scenario_gen_base sgen,
                                     string str_idx,
                                     vmm_data tr);
        vmm_ss_scenario_base scn;
        int idx = -1;
        scn = get_scenario_by_name(sname, sgen);
        if (scn == null) return;
        if (str_idx != "*") begin
           idx = str_idx.atoi();
        end
        if (fact_type == CREATE_COPY)  scn.Xset_allocate_idX(tr.copy(), idx); 
        else scn.Xset_allocate_idX(tr.allocate(), idx);
   endfunction

   function void split_hiername(string pattern,
                                output string name, 
                                output string hier_pat);
      string one_char;
      string var_name;
      int len = pattern.len();
      for (int i=len-1; i>=0; i--) begin
		 
		 `ifndef MACRO_CAST 
         one_char = `_TO_CAST_TO_STRING(pattern.getc(i));
		 `else
		  $cast(one_char,pattern.getc(i));
		 `endif
		 
         if (one_char == ":") begin
           hier_pat = pattern.substr(0, i-1);
           name = var_name;
           return;
         end
         else if (one_char == "%") begin
           hier_pat = pattern.substr(0, i);
           name = var_name;
           return;
         end
         var_name = {one_char, var_name};
      end
      name = var_name;
   endfunction

endclass



`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_factory_cache#(type classname = vmm_object);

   vmm_factory_pattern_info #(classname) regex_cache[string];

   function classname get_factory(string path);
     if (regex_cache.exists(path)) begin
        classname inst;
        classname factory = regex_cache[path].factory;
        if (regex_cache[path].fact_type == vmm_factory_base_pattern_info::CREATE_NEW) begin
           $cast(inst, factory.allocate());
        end
        else begin
           $cast(inst, factory.copy());
        end
        return inst;
     end
   endfunction

   function void add_new_entry(vmm_factory_pattern_info #(classname) fact, string path);
      regex_cache[path] = fact;
   endfunction
   
   function void refresh_cache(vmm_factory_pattern_info #(classname) fact);
      foreach (regex_cache[str]) begin
        if (vmm_path_match::match(str, fact.regexp)) begin
           regex_cache[str] = fact;
        end
      end
   endfunction

endclass

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_class_factory_base#(type classname=vmm_object);
   static /*local*/ vmm_factory_pattern_info #(classname) XpatternXQ[$];
   static local classname XctypeX;
   static vmm_factory_cache#(classname) cache = new();
 
   static function classname Xfactory_typeX(output bit first_obj_flg);
      vmm_unit unit;
      if (XctypeX == null) begin
         XctypeX = new();
         first_obj_flg = 1'b1;
         if ($cast(unit, XctypeX)) 
           unit.implicit_phasing(0);
      end
      return XctypeX;
   endfunction

   static function classname create_instance(vmm_object parent, 
                                             string name,
                                             string fname = "",
                                             int lineno   = 0);
      classname inst;
      `vmm_path_compiled comp_path;
      vmm_object obj;
      vmm_data dta;
      vmm_unit   unit;
      vmm_log log;
      bit first_obj_flg;
      if (parent != null) log = parent.get_log();
      else log = new(name, "create_instance");
      comp_path = vmm_path_match::compile_path(log, parent, name);
      //Fast path using cache
      inst = cache.get_factory(comp_path);
      if (inst != null) begin
         if ($cast(obj, inst)) begin
            obj.set_object_name(name);
            if (!$cast(dta, inst)) begin
               obj.set_parent_object(parent);
            end
         end
         return inst;
      end
      //Slow path without using cache
      foreach (XpatternXQ[i]) begin
         if (vmm_path_match::match(comp_path, XpatternXQ[i].regexp)) begin
            vmm_factory_pattern_info #(classname) fact = XpatternXQ[i];
            classname factory = fact.factory;
            if (fact.fact_type == vmm_factory_base_pattern_info::CREATE_NEW) begin
                  if (!$cast(inst, factory.allocate())) begin
						`ifndef VMM_NO_TYPENAME 
                     	   `VMM_FATAL({"factory.allocate() should return instance of type ", $typename(classname)}, fname, lineno);
						`else 
                     	   `VMM_FATAL({"factory.allocate() should return instance of type ", ""}, fname, lineno);
						`endif 

                  end
                  if ($cast(obj, inst)) begin
                     obj.set_object_name(name);
                     if (!$cast(dta, inst)) begin
                        obj.set_parent_object(parent);
                     end
                  end
            end
            else begin
               if (!$cast(inst, factory.copy())) begin
						`ifndef VMM_NO_TYPENAME 
                     	   `VMM_FATAL({"factory.copy() should return instance of type ", $typename(classname)}, fname, lineno);
						`else 
                     	   `VMM_FATAL({"factory.copy() should return instance of type ", ""}, fname, lineno);
						`endif 
               end
               if ($cast(obj, inst)) begin
                  obj.set_object_name(name);
                  if (!$cast(dta, inst)) begin
                     obj.set_parent_object(parent);
                  end
               end
            end
            cache.add_new_entry(fact, comp_path);
            if (parent == null) log.kill();
            return inst;
         end 
      end
      inst = Xfactory_typeX(first_obj_flg);
      if (!first_obj_flg) 
        $cast(inst, inst.allocate());
      else
        if ($cast(unit, inst))
           unit.implicit_phasing(1);
      if ($cast(obj, inst)) begin
         obj.set_object_name(name);
         if (!$cast(dta, inst)) begin
            obj.set_parent_object(parent);
         end
      end
      if (parent == null) log.kill();
      return inst;
   endfunction

   static function void override_with_new(string name, 
                                      classname factory,
                                      vmm_log log,
                                      string fname = "",
                                      int lineno   = 0);
      vmm_factory_pattern_info#(classname) fact;
      bit null_log;
      if (log == null) begin
         log = new("override_with_new", name);
         null_log = 1;
      end
      if (factory == null) begin
        `VMM_FATAL("override_with_new called with null factory instance of class classname ", fname, lineno);
      end
      fact = new(name, factory, vmm_factory_base_pattern_info::CREATE_NEW, fname, lineno);
      fact.regexp  = vmm_path_match::compile_pattern(name, log);
      fact.check_n_replace_gen_factory(log);
      factory.Xadd_patternX(fact);
      cache.refresh_cache(fact);
      if (null_log) log.kill();
   endfunction

   static function void override_with_copy(string name, 
                                       classname factory,
                                       vmm_log log,
                                       string fname = "",
                                       int lineno   = 0);
      vmm_factory_pattern_info#(classname) fact;
      bit null_log;
      if (log == null) begin
         log = new("override_with_copy", name);
         null_log = 1;
      end
      if (factory == null) begin
        `VMM_FATAL("override_with_copy called with null factory instance of class classname", fname, lineno);
      end
      fact = new(name, factory, vmm_factory_base_pattern_info::CREATE_COPY, fname, lineno);
      fact.regexp  = vmm_path_match::compile_pattern(name, log);
      fact.check_n_replace_gen_factory(log);
      factory.Xadd_patternX(fact);
      cache.refresh_cache(fact);
      if (null_log) log.kill();
   endfunction

endclass

//`endif //NO_VMM12_PARAM_CHANNEL
