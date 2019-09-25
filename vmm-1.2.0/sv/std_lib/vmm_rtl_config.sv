class vmm_rtl_config_phase_build_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_build_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.build_config_ph();
   endfunction
endclass

class vmm_rtl_config_phase_get_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_get_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.get_config_ph();
   endfunction
endclass

class vmm_rtl_config_phase_save_cfg_ph_def extends vmm_topdown_function_phase_def #(vmm_rtl_config);
   `vmm_typename(vmm_rtl_config_phase_save_cfg_ph_def)
   virtual function void do_function_phase(vmm_rtl_config obj);
      obj.save_config_ph();
   endfunction
endclass

function void vmm_rtl_config_phase_def::run_function_phase(string name, vmm_object obj, vmm_log log);
   bit is_set;
   vmm_rtl_config robj;

   if (!$cast(robj, obj)) begin
     return;
   end
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



function vmm_rtl_config::new(string name = "", vmm_rtl_config parent = null);
   super.new(parent, name);
   log = new(get_typename(), name);
endfunction

function void vmm_rtl_config::map_to_name(string name);
   this.set_object_name(name, "VMM RTL Config");
endfunction: map_to_name

function void vmm_rtl_config::build_config_ph();
endfunction: build_config_ph

function void vmm_rtl_config::get_config_ph();
   load_save_config(LOAD); //load the configuration
endfunction: get_config_ph

function void vmm_rtl_config::save_config_ph();
   load_save_config(SAVE); //save the configuration
endfunction: save_config_ph

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

function string vmm_rtl_config_file_format::fname(vmm_rtl_config cfg);
    string filename = {cfg.XprefixX, "/", cfg.get_object_hiername(), ".cfg"};
   for (int i=0; i<filename.len(); i++) begin
     if (filename.getc(i) == ":") filename = {filename.substr(0, i-1), "/", filename.substr(i+1, filename.len()-1)};
   end
   return filename;
endfunction

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
       string char1 = line.getc(i);
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


`define vmm_rtl_config_begin(classname) \
   virtual function void load_save_config(mode_e load_param); \
      int f; \
      string mode = (load_param==LOAD) ? "r" : "w"; \
      if (this.Xload_save_doneX) return; \
      if (Xfile_ptrX <= 0) begin \
         if (file_fmt == null) begin \
            `vmm_debug(log, "File format not specified for accessing rtl configuration files, using default file format.."); \
            if (default_file_fmt == null) begin \
              vmm_rtl_config_default_file_format fmt = new; \
              default_file_fmt = fmt; \
              `vmm_debug(log, "Default file format is not specified for accessing rtl configuration files"); \
              return; \
            end \
            file_fmt = default_file_fmt; \
         end \
        if (!file_fmt.fopen(this, mode, `__FILE__, `__LINE__)) begin \
            `vmm_fatal(log, {"Unable to open file in ", mode, " mode for config instance ", this.get_object_hiername()});  \
              return; \
         end \
         f = 1; \
      end

`define vmm_rtl_config_boolean(name, fname) \
   begin \
      if (load_param == LOAD) begin \
         if (!file_fmt.read_bit(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't read `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
      else begin \
         if (!file_fmt.write_bit(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't write `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
   end

`define vmm_rtl_config_int(name, fname) \
   begin \
      if (load_param == LOAD) begin \
         if (!file_fmt.read_int(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't read `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
      else begin \
         if (!file_fmt.write_int(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't write `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
   end

`define vmm_rtl_config_string(name, fname) \
   begin \
      if (load_param == LOAD) begin \
         if (!file_fmt.read_string(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't read `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
      else begin \
         if (!file_fmt.write_string(`"fname`", this.name)) begin \
            `vmm_fatal(log, {`"Couldn't write `", `"fname`", `" for variable `", `"name`"}); \
              return; \
         end \
      end \
   end

`define vmm_rtl_config_obj(name) \
    if (obj != null) obj.load_save_config(load_param);


`define vmm_rtl_config_end(classname) \
     if (f) file_fmt.fclose(); \
     this.Xload_save_doneX = 1; \
   endfunction


