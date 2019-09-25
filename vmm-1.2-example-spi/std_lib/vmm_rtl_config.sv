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

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_rtl_config_phase_build_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_build_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.build_config_ph();
   endfunction
endclass

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_rtl_config_phase_get_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_get_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.get_config_ph();
   endfunction
endclass

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_rtl_config_phase_save_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_save_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.save_config_ph();
   endfunction
endclass

function void vmm_rtl_config_phase_def::run_function_phase(string name, vmm_object obj, vmm_log log);
   bit            is_set;
   vmm_rtl_config robj;
   vmm_object     child;
   vmm_timeline   tl;
   vmm_unit       mod1;
   int            i;

   if ($cast(robj, obj)) begin
      if (robj.XprefixX == "") begin
         `vmm_trace(log, "RTL Configuration Not Enabled");
         return;
      end
      build_cfg_ph = new;
      build_cfg_ph.run_function_phase("rtl_config_build_config", robj, log);
      if (robj.Xgen_rtl_configX) begin
         if (!robj.randomize()) begin
            `vmm_fatal(log, "RTL Configuration Generation failed due to randomization failure");
         end
         save_cfg_ph = new;
         save_cfg_ph.run_function_phase("rtl_config_save_config", robj, log);
         `vmm_note(log, "RTL Configuration Generated, exiting simulation..");
         log.report();
         $finish;
      end
      get_cfg_ph = new;
      get_cfg_ph.run_function_phase("rtl_config_get_config", robj, log);
   end
   i = 0;
   child = obj.get_nth_child(i++);
   while (child != null) begin
      if ($cast(tl, child)) begin
         tl.run_function_phase(name);
      end
      else if($cast(mod1,child))begin
         vmm_timeline t2;
	 t2 = mod1.get_timeline();
	 if(!mod1.is_unit_enabled() && mod1.phase_executed["reset"]) ;
         else begin
	    if(mod1.override_phase_defs.exists(name)) begin
	       `vmm_debug(log,`vmm_sformatf( "Using new definition of phase %s for %s(%s) ",name,mod1.get_object_name(),mod1.get_typename()));
	       mod1.override_phase_defs[name].run_function_phase(name, mod1, log);
	    end
	    else this.run_function_phase(name, mod1, log);
	 end
      end
      else this.run_function_phase(name, child, log);
      child = obj.get_nth_child(i++);
   end
endfunction

task vmm_rtl_config_phase_def::run_task_phase(string name, vmm_object obj, vmm_log log);
   `vmm_fatal(log,
              `vmm_sformatf("Internal error: %s::run_task_phase() called instead of %s::run_function_phase()",
                            this.get_typename(), this.get_typename()));

endtask

function bit vmm_rtl_config_phase_def::is_function_phase();
   return 1;
endfunction:is_function_phase

function bit vmm_rtl_config_phase_def::is_task_phase();
   return 0;
endfunction:is_task_phase



// Class: vmm_rtl_config
//
// This is the base class for RTL configuration and extends vmm_object. This class is 
// for specifying RTL configuration parameters. A different class from other parameters 
// that use the vmm_opts class is used, because these parameters must be defined 
// at compile time and may not be modified at runtime.
//
// Example
//| class ahb_master_config extends vmm_rtl_config;
//|   rand int addr_width;
//|   rand bit mst_enable;
//|   string kind = "MSTR";
//|   constraint cst_mst {
//|     addr_width == 64;
//|     mst_enable == 1;
//|   }
//|   `vmm_rtl_config_begin(ahb_master_config)
//|   `vmm_rtl_config_int(addr_width, mst_width)
//|   `vmm_rtl_config_boolean(mst_enable, mst_enable)
//|   `vmm_rtl_config_string(kind, kind)
//|
//|   `vmm_rtl_config_end(ahb_master_config)
//|   function new(string name = "", vmm_rtl_config parent = null);
//|     super.new(name, parent);
//|   endfunction
//| endclass

    
function vmm_rtl_config::new(string name = "", vmm_rtl_config parent = null);
   super.new(parent, name);
   log = new(get_typename(), name);
endfunction

// //////////////////////////////////////////// 
// Function: map_to_name 
// 
//|    function void map_to_name(string name)
// 
// Use the specified name for this instance of the configuration descriptor, instead
// of the object name, when looking for relevant vmm_rtl_config instances in the RTL configuration
// hierarchy. The specified name is used as the object name in the VMM RTL Config namespace.
// When argument name is passed as caret (^) for any particular configuration descriptor,
// that configuration descriptor becomes a root object under "VMM RTL Config". 
// 
//|   class ahb_master_config extends vmm_rtl_config;
//|      function new(string name = "", vmm_rtl_config parent =
//|            null);
//|         super.new(name, parent);
//|      endfunction
//|   endclass
//|   
//|   class env_config extends vmm_rtl_config;
//|      rand ahb_master_config mst_cfg;
//|      function void build_config_ph();
//|         mst_cfg = new("mst_cfg", this);	
//|      endfunction
//|   endclass
//|   
//|   initial begin
//|      env_config env_cfg = new("env_cfg");
//|      env_cfg.mst_cfg.map_to_name("env:mst"); 
//|   end
function void vmm_rtl_config::map_to_name(string name);
   this.set_object_name(name, "VMM RTL Config");
endfunction: map_to_name

// //////////////////////////////////////////// 
// Function: build_config_ph 
// 
// Builds the structure of RTL configuration parameters for hierarchical RTL designs.
// 
// 
//|   class env_config extends vmm_rtl_config;
//|      rand ahb_master_config mst_cfg;
//|      rand ahb_slave_config  slv_cfg;
//|      ...
//|      function void build_config_ph();
//|         mst_cfg = new("mst_cfg", this);
//|         slv_cfg = new("slv_cfg", this);
//|      endfunction
//|      ...
//|   endclass 
function void vmm_rtl_config::build_config_ph();
endfunction: build_config_ph

// //////////////////////////////////////////// 
// Function: get_config_ph 
// 
// Reads a configuration file and sets the current value of members to the corresponding
// RTL configuration parameters. The filename may be computed using the value of the +vmm_rtl_config
// option, using the vmm_opts::get_string("rtl_config") method and the hierarchical
// name of this vmm_object instance. 
// A default implementation of this method is created, if the `vmm_rtl_config_*() shorthand
// macros are used. 
// vmm_rtl_config_* 
// 
function void vmm_rtl_config::get_config_ph();
   load_save_config(LOAD); //load the configuration
endfunction: get_config_ph

// //////////////////////////////////////////// 
// Function: save_config_ph 
// 
// Creates a configuration file that specifies the RTL configuration parameters corresponding
// to the current value of the class members. The filename may be computed using the value
// of the +vmm_rtl_config option, using the vmm_opts::get_string("rtl_config") method
// and the hierarchical name of this vmm_object instance. 
// A default implementation of this method is created, if the `vmm_rtl_config_*() shorthand
// macros are used. 
// 
function void vmm_rtl_config::save_config_ph();
   load_save_config(SAVE); //save the configuration
endfunction: save_config_ph

// //////////////////////////////////////////// 
// Function: get_config 
// 
// Gets the instance of the specified class extended from the vmm_rtl_config class, whose
// hierarchical name in the VMM RTL Config namespace is identical to the hierarchical
// name of the specified object. This allows a component to retrieve its instance-configuration,
// without having to know where it is located in the testbench hierarchy. 
// The fname and lineno arguments are used to track the file name and the line number where
// get_config is invoked from. 
// 
//|   class ahb_master extends vmm_group;
//|      ahb_master_config cfg; 
//|      function void configure_ph();
//|         $cast(cfg, get_config(this, 
//|            `__FILE__, `__LINE__));
//|      endfunction
//|   endclass 
function vmm_rtl_config vmm_rtl_config::get_config(vmm_object uobj, string fname = "", int lineno = 0);
   vmm_object comp_obj = uobj;
   vmm_object tobj;
   vmm_rtl_config rcfg;
   int i =0;
   string hier = uobj.get_object_hiername();
   tobj = vmm_object::get_nth_root(i);
   while (tobj != null) begin
     if ($cast(rcfg, tobj)) begin
        `foreach_vmm_object(vmm_rtl_config, "@%*", rcfg) begin
           string conf_hier = obj.get_object_hiername(, "VMM RTL Config");
           if (conf_hier.getc(0) == "^") conf_hier = conf_hier.substr(2,hier.len()-1);
           if (conf_hier == hier) return obj;
        end
     end
     i++;
     tobj = vmm_object::get_nth_root(i);
   end
/*
   tobj = vmm_object::find_object_by_name(uobj.get_object_hiername(), "VMM RTL Config");
   if (tobj != null && $cast(rcfg, tobj)) return rcfg;
*/
endfunction: get_config

function void vmm_rtl_config::load_save_config(mode_e load_param);
endfunction: load_save_config

// //////////////////////////////////////////// 
// Class: vmm_rtl_config_file_format
//
// This is the base class for RTL configuration file writer or parser. May be used to 
// simplify the task of implementing the <vmm_rtl_config::get_config_ph> and 
// <vmm_rtl_config::save_config_ph> methods.
//    
// Function: fname 
// 
//|    virtual protected function string 
//|       fname(vmm_rtl_config cfg)
// 
// Computes the filename that contains the RTL configuration parameter for the specified
// instance of the RTL configuration descriptor. By default, concatenates the value
// of the +vmm_rtl_config option and the hierarchical name of the specified RTL configuration
// descriptor, separating the two parts with a slash (/) and appending a .cfg suffix. 
// 
function string vmm_rtl_config_file_format::fname(vmm_rtl_config cfg);
    string filename = {cfg.XprefixX, "/", cfg.get_object_hiername(), ".cfg"};
   for (int i=0; i<filename.len(); i++) begin
     if (filename.getc(i) == ":") filename = {filename.substr(0, i-1), "/", filename.substr(i+1, filename.len()-1)};
   end
   return filename;
endfunction

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

// //////////////////////////////////////////// 
// Class: vmm_rtl_config_default_file_format
//
// Default implementation for RTL config file format 
//    
// Function: fname 
// 
//|    virtual protected function string 
//|       fname(vmm_rtl_config cfg)
// 
// Computes the filename that contains the RTL configuration parameter for the specified
// instance of the RTL configuration descriptor. By default, concatenates the value
// of the +vmm_rtl_config option and the hierarchical name of the specified RTL configuration
// descriptor, separating the two parts with a slash (/) and appending a .cfg suffix. 
// 
class vmm_rtl_config_default_file_format extends vmm_rtl_config_file_format;
  local  string   cfg_fname;
  local  int      cfg_lineno;
  static vmm_log  log = new("vmm_rtl_config_default_file_format", "class"); 

  virtual function bit fopen(vmm_rtl_config cfg, 
                             string mode, 
                             string fname = "", 
                             int lineno = 0);
    cfg_fname = this.fname(cfg);
    vmm_rtl_config::Xfile_ptrX = $fopen(cfg_fname, mode);
    if (vmm_rtl_config::Xfile_ptrX == 0) return 0;
    else return 1;
  endfunction

  local function string get_next_line(int fp);
    string line;
    if ($fgets(line, fp)) begin
       cfg_lineno++;
       while (line.getc(0) == " ") line = line.substr(1, line.len()-1);
       for (int i=0; i<line.len(); i++) begin
         if ((line.getc(i) == "#") || (line.getc(i) == ";")) begin
            line = line.substr(0, i-1); break;
         end
       end
       return line;
    end
  endfunction

  local function bit get_val(string name, output string val_str);
    string line;
    string str_name, str_val;
    bit name_done;
    line = get_next_line(vmm_rtl_config::Xfile_ptrX);
    if (line == "") return 0;
    for (int i=0; i<line.len(); i++) begin
       string char1;
	   char1 = `_TO_CAST_TO_STRING(line.getc(i));
       if (char1 == " ") continue;
       if (char1 == ":") begin
          name_done = 1; continue;
       end
       if (name_done) str_val = {str_val, char1};
       else str_name = {str_name, char1};
    end
    if (str_name != name) `vmm_fatal(log, `vmm_sformatf("Expected name mismatch while reading rtl_config file %s, line %0d, expected %s, actual %s", 
            cfg_fname, cfg_lineno, name, str_name));
    val_str = str_val;
    return 1;
  endfunction

  virtual function bit read_bit(string name, output bit value);
    string str;
    bit r = get_val(name, str);
    value = str.atoi();
    return r;
  endfunction

  virtual function bit read_int(string name, output int value);
    string str;
    bit r = get_val(name, str);
    value = str.atoi();
    return r;
  endfunction

  virtual function bit read_string(string name, output string value);
    read_string = get_val(name, value);
  endfunction

  virtual function bit write_bit(string name, bit value);
    $fwrite(vmm_rtl_config::Xfile_ptrX, "%s     : %b;\n", name, value);
    return 1;
  endfunction

  virtual function bit write_int(string name, int value);
    $fwrite(vmm_rtl_config::Xfile_ptrX, "%s     : %0d;\n", name, value);
    return 1;
  endfunction

  virtual function bit write_string(string name, string value);
    $fwrite(vmm_rtl_config::Xfile_ptrX, "%s     : %s;\n", name, value);
    return 1;
  endfunction

  virtual function void fclose();
    $fclose(vmm_rtl_config::Xfile_ptrX);
  endfunction

endclass


