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

function vmm_opts_info::new(string opt, string sarg = "");
   this.opt = opt;
   this.sarg = sarg;
   if (opt.len() > width) width = opt.len();
endfunction: new

function string vmm_opts_info::help(bit [12:0] id, bit is_used=0);
      static string spaces = "                                          ";
      string fmt;
      string pad = spaces.substr(0, width-opt.len()-1);
      string txt;

      if (this.opt_specified) begin
         case (src_type)
          CMD_LINE: txt = "Command Line";
          CMD_FILE: txt = $psprintf("Option File %s line %0d", fname, lineno);
          SV_FILE : txt = $psprintf("File %s line %0d", fname, lineno);
         endcase
         if (arg_specified)
          txt = {sarg, " - Specified via ", txt};
         else
          txt = {"Specified via ", txt};
      end
      else begin
         txt = "Unspec'd";
      end
      if (this.exp_hier != "")
          txt = {txt, ", Needed for Object Hierarchy ", exp_hier};
      else
          txt = {txt, ", Needed for Any Hierarchy"};
      if (is_used) begin
         if (is_expected) begin  //option is needed and has been used 
            case (arg_type)
              BOOL_ARGS:  $sformat(fmt, "%d) %s%s       (%s) : %s",
                                 id, opt, pad, txt, doc);
              STR_ARGS: $sformat(fmt, "%d) %s%s=<str> (%s) : %s",
                                 id, opt, pad, txt, doc);
              INT_ARGS: $sformat(fmt, "%d) %s%s=<int> (%s) : %s",
                                 id, opt, pad, txt, doc);
              RANGE_ARGS: $sformat(fmt, "%d) %s%s=[<min>:<max>] (%s) : %s",
                                 id, opt, pad, txt, doc);
            endcase
         end
         else begin //option is needed but ignored due to lesser priority
            $sformat(fmt, "%d) %s%s       (%s, Ignored)", id, opt, pad, txt);
         end
      end
      else begin
         $sformat(fmt, "%d) %s%s       (%s, Not Used Anywhere So far)", id, opt, pad, txt);
      end
      return fmt;
endfunction: help


//`ifdef VMM_12
function string vmm_opts_info::psdisplay(string prefix = "");
//todo
   string result;
   result = `vmm_sformatf("----------------- %s %s ----------------\n", prefix, opt);
   if (opt_specified) begin
      string txt;
      case (src_type)
       CMD_LINE: txt = "Command Line";
       CMD_FILE: txt = $psprintf("Command File %s (%0d)", fname, lineno);
       SV_FILE : txt = $psprintf("File %s (%0d)", fname, lineno);
      endcase
      result = {result, "\n\tSPECIFIED through : ", txt};
      if (arg_specified)
        result = {result, "\n\tArgument : ", sarg};
      if (pat_specified)
        result = {result, "\n\tOption is Hierarchical (", hier, ")\n"};
      else
        result = {result, "\n\tOption is Global\n"};
   end
   else begin
      result = {result, "\tOption Not Specified anywhere\n"};
   end
   if (is_expected) begin
     result = {result, `vmm_sformatf("\tEXPECTED (by get_.. method) argument type %s", arg_type.name)};
     result = {result, `vmm_sformatf("\tVerbosity level = %0d\n", verbosity)};
   end
   else begin
      result = {result, "\tOption Not Used anywhere so far\n"};
   end
  
   return result;               
endfunction: psdisplay
//`endif
  
//Holds a set of options with the same option name and prioritize them when required
class vmm_opts_info_wrapper;
   vmm_opts_info oinfo_q[$]; //todo should be local
   string name;
   bit is_used;
   vmm_log log;

   function new(string name, vmm_log log);
     this.name = name;
     this.log = log;
   endfunction

   //Adds/updates specified option
   function void add_option(vmm_opts_info oinfo);
      foreach (oinfo_q[i]) begin
        if (oinfo.src_type == oinfo_q[i].src_type &&
            oinfo.opt_specified &&
            oinfo.hier     == oinfo_q[i].hier) begin
            oinfo_q[i] = oinfo;
            return;
        end
      end
      oinfo_q.push_back(oinfo);
      `vmm_verbose(log, oinfo.psdisplay("Adding Specified Option:"));
   endfunction

   function vmm_opts_info get_option(string hier = "");
     vmm_opts_info oinfo;

     oinfo = get_opts_from_type(vmm_opts_info::CMD_LINE, hier);
     if (oinfo == null) oinfo = get_opts_from_type(vmm_opts_info::CMD_FILE, hier);
     if (oinfo == null) oinfo = get_opts_from_type(vmm_opts_info::SV_FILE, hier);
     if (oinfo == null) begin //Option is not specified
       oinfo = new(this.name); 
     end
     oinfo.exp_hier = hier;
     oinfo.is_expected = 1;
     get_option =  oinfo;
     is_used = 1; 
   endfunction

   local function vmm_opts_info get_opts_from_type(vmm_opts_info::src_type_e src_type, string hier);
      vmm_opts_info match_opts[$];
      match_opts = oinfo_q.find(idx) with ( idx.src_type == src_type && idx.opt_specified );
      foreach (match_opts[i]) begin
        `vmm_path_compiled comp_path;
        if (match_opts[i].hier == "") return match_opts[i];
        if (match_opts[i].pat_specified) begin //hierarchical option
           if (match_opts[i].hier == hier) return match_opts[i];
           comp_path = vmm_path_match::compile_path(log, null, hier);
           if (vmm_path_match::match(comp_path, match_opts[i].regexp)) begin
             `vmm_verbose(log, `vmm_sformatf("Path %s and Pattern %s matching.. ", hier, match_opts[i].hier));
             return match_opts[i];
           end
           else begin
             `vmm_verbose(log, `vmm_sformatf("Path %s and Pattern %s NOT matching", hier, match_opts[i].hier));
           end
        end
      end
   endfunction
 
endclass

function bit vmm_opts::extract_opts_info();
   if (opts_extracted) return 1;
   opts_extracted = 1;

   log = new("vmm_opts", "class");
   //log.set_verbosity(vmm_log::TRACE_SEV); //todo

   // Option files first
   if ($test$plusargs("vmm_opts_file")) begin
      string format;
      if ($value$plusargs("vmm_opts_file+%s", format)) begin
         string opts_file[$];
         void'(split(format, opts_file));      
         foreach (opts_file[i]) begin
            parse_opts_file(opts_file[i]);
         end
      end
   end

   // Command-line overrides option file options
   if ($test$plusargs("vmm_opts+")) begin
      string format;
      string txt;
      if ($value$plusargs("vmm_opts+%s", format)) begin
         string opts[$];
         void'(split(format, opts));      
         foreach (opts[i]) begin
            txt = {txt, "\t ", opts[i], "\n"};
            add_specified_option(opts[i], "", vmm_opts_info::CMD_LINE);
         end
         `vmm_verbose(log, {"List of options specified through +vmm_opts+ are:\n", txt});
      end
   end
endfunction


function void vmm_opts::parse_opts_file(string filename, string prefix = "");
   string t_str;
   int    fp;
   int    lineno;
   string fname = filename;
   string file_hier = prefix;

   if (`vmm_str_match(filename, "@")) begin
     string tmpstr;
     fname = `vmm_str_prematch(filename);
     tmpstr = `vmm_str_postmatch(filename);
     if (prefix != "") file_hier = {prefix, ":", tmpstr};
     else file_hier = tmpstr;
   end
   fp = $fopen(fname, "r"); 
   if (!fp) begin
      `vmm_fatal(log, `vmm_sformatf("Unable to open options file %s for reading", fname));
      return;
   end

   while ($fgets(t_str, fp)) begin
      t_str = t_str.substr(0, t_str.len()-2);
      lineno++;
      if (`vmm_str_match(t_str, "^#")) continue;
      else if (`vmm_str_match(t_str, "import")) begin
         string fstr;
         fstr = `vmm_str_postmatch(t_str);
         while (fstr.getc(0) == " ") fstr = fstr.substr(1, fstr.len()-1);
         if (fstr != "") begin
            parse_opts_file(fstr, file_hier);
         end
      end
      else begin
        while (t_str != "") begin
           string str;
           bit option_start;
           for (int i=0; i<t_str.len(); i++) begin
              string onec = t_str.getc(i);
              if (onec == "+") begin
                 option_start = 1; continue;
              end
              if (onec == " ") begin
                 option_start = 0; 
                 t_str = t_str.substr(i+1, t_str.len()-1);
                 break;
              end
              if (onec == "#") begin
                 option_start = 0; t_str = ""; break;
              end
              if (option_start) begin
                str = {str, onec};
              end
              if (i==t_str.len()-1) begin
                 t_str = ""; break;
              end
           end
           if (str != "") begin
              if (file_hier != "") begin //file is specified with hierarchy
                 string hier;
                 if (`vmm_str_match(str, "@")) begin
                     hier = `vmm_str_postmatch(str);
                     str  = `vmm_str_prematch(str);
                     hier = {file_hier, ":", hier};
                 end
                 else begin
                     hier = file_hier;
                 end
                 str = {str, "@", hier};
              end
              add_specified_option(str, fname, vmm_opts_info::CMD_FILE, lineno);
           end
        end
      end
   end

   $fclose(fp);
endfunction

function void vmm_opts::add_specified_option(string frmt,
                                             string fname = "Command Line",
                                             vmm_opts_info::src_type_e src_type,
                                             int lineno = 0);
   bit arg_specified;
   bit pat_specified;
   int val;
   int idx[$];
   string s_arg;
   string hier;
   string name;
   string tmp_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   arg_specified = 0;
   if (`vmm_str_match(frmt, "=")) begin
      s_arg = `vmm_str_postmatch(frmt);
      frmt = `vmm_str_prematch(frmt);
      arg_specified = 1;
      tmp_str = s_arg;
      if (`vmm_str_match(tmp_str, "@")) begin //checking if there is hierarchy
        pat_specified = 1;
        hier = `vmm_str_postmatch(tmp_str);
        s_arg = `vmm_str_prematch(tmp_str);
      end
   end
   else begin //option without argument
      tmp_str = frmt;
      if (`vmm_str_match(tmp_str, "@")) begin //checking if there is hierarchy
        pat_specified = 1;
        hier = `vmm_str_postmatch(tmp_str);
        frmt = `vmm_str_prematch(tmp_str);
      end
   end


   oinfo = new(frmt, s_arg);
   if (arg_specified) oinfo.sarg = s_arg;

   oinfo.opt_specified = 1;
   oinfo.src_type      = src_type;
   oinfo.arg_specified = arg_specified;
   oinfo.pat_specified = pat_specified;
   oinfo.hier          = hier;
   oinfo.fname         = fname;
   oinfo.lineno        = lineno;


   //Compiling the regexp
   if (oinfo.pat_specified) begin
     oinfo.regexp = vmm_path_match::compile_pattern({"@", oinfo.hier}, log);
   end

   if (opts_info.exists(frmt)) begin
      oinfow = opts_info[frmt];
   end
   else begin
      oinfow = new(frmt, log);
      opts_info[frmt] = oinfow;
   end

   oinfow.add_option(oinfo);

endfunction

function vmm_opts_info vmm_opts::get_opts_by_name(string name, 
                                                  vmm_opts_info::arg_type_e arg_type, 
                                                  int verbosity, 
                                                  string doc, 
                                                  string hier = "");
   string vname = {"vmm_", name};
   string format;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;
   bit bad_rng;
   int idx[$];

   if (!opts_extracted)
      void'(extract_opts_info());

   if (opts_info.exists(name)) begin
      oinfow = opts_info[name];
   end
   else begin
      oinfow = new(name, log);
      opts_info[name] = oinfow;
   end

   if ($test$plusargs(vname)) begin
      string sarg, format, hier, tmp_str;
      oinfo = new(name);
      oinfo.opt_specified = 1;
      oinfo.src_type      = vmm_opts_info::CMD_LINE;
      format = `vmm_sformatf("vmm_%s=%%s", name);
      if ($value$plusargs(format, sarg)) begin
         oinfo.sarg = sarg;
         oinfo.arg_specified = 1;
         if (`vmm_str_match(sarg, "@")) begin //checking if there is hierarchy
           oinfo.pat_specified = 1;
           oinfo.hier = `vmm_str_postmatch(sarg);
           oinfo.sarg = `vmm_str_prematch(sarg);
         end
      end
      else begin //check hierarchy without =
         format = `vmm_sformatf("vmm_%s@%%s", name);
         if ($value$plusargs(format, hier)) begin
            oinfo.hier = hier;
            oinfo.pat_specified = 1;
         end
      end
      //Compiling the regexp
      if (oinfo.pat_specified) begin
        oinfo.regexp = vmm_path_match::compile_pattern({"@", oinfo.hier}, log);
      end
    
      oinfow.add_option(oinfo);
   end


   //Now get the prioritized option
   oinfo           = oinfow.get_option(hier);
   oinfo.arg_type  = arg_type;
   oinfo.verbosity = verbosity;
   oinfo.doc       = doc;
   if (arg_type == vmm_opts_info::INT_ARGS) oinfo.val = oinfo.sarg.atoi();
   if (arg_type == vmm_opts_info::RANGE_ARGS && oinfo.opt_specified) begin
      string str = oinfo.sarg;
      if (str.getc(0) != "[" || str.getc(str.len()-1) != "]") bad_rng = 1;
      str = str.substr(1, str.len()-1);
      if (`vmm_str_match(str, ":")) begin //todo
         string tmp_str;
         tmp_str = `vmm_str_prematch(str);
         oinfo.min = tmp_str.atoi();
         tmp_str = `vmm_str_postmatch(str);
         oinfo.max = tmp_str.atoi();
      end
      else begin
        bad_rng = 1;
      end
      if (bad_rng) begin
        `vmm_fatal(log, `vmm_sformatf("Illegal range argument specified %s , expected format [min:max] where min and max are minimum and maximum values of the range", oinfo.sarg));
      end
   end
   if (verbosity > 10) begin
      `vmm_warning(log, `vmm_sformatf("Verbosity (%0d) exceeding the limit (10) for the option %s", verbosity, name));
   end


   `vmm_verbose(log, oinfo.psdisplay("Getting Expected Option:"));
   return oinfo;

endfunction

function bit    vmm_opts::get_bit(string name,
                                  string doc = "",
                                  int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::BOOL_ARGS, verbosity, doc);
   return oinfo.opt_specified;
endfunction

function string vmm_opts::get_string(string name,
                                     string dflt,
                                     string doc = "",
                                     int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::STR_ARGS, verbosity, doc);
   if (oinfo.arg_specified) return oinfo.sarg;
   return dflt;
endfunction

function int    vmm_opts::get_int(string  name,
                                  int     dflt = 0,
                                  string  doc = "",
                                  int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::INT_ARGS, verbosity, doc);
   if (oinfo.arg_specified) return oinfo.val;

   return dflt;
endfunction

function void   vmm_opts::get_range(string  name,
                                    output int min, max,
                                    input  int dflt_min, dflt_max,
                                    string  doc  = "",
                                    int verbosity = 0,
                                    string fname = "",
                                    int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::RANGE_ARGS, verbosity, doc);
   if (oinfo.arg_specified) begin
       min = oinfo.min;
       max = oinfo.max;
       return;
   end
   min = dflt_min;
   max = dflt_max;
endfunction

function vmm_object  vmm_opts::get_obj(output bit is_set,
                                       input string  name,
                                       input vmm_object dflt = null,
                                       string fname = "",
                                       int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::OBJ_ARGS, 0, "");
   if (oinfo.arg_specified) begin
     is_set = 1;
     return oinfo.obj;
   end
   return dflt;
endfunction

function bit    vmm_opts::get_object_bit(output bit is_set,
                                         input vmm_object obj,
                                         string name,
                                         string doc = "",
                                         int verbosity = 0,
                                         string fname = "",
                                         int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_bit called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::BOOL_ARGS, verbosity, doc, obj.get_object_hiername());
   is_set = oinfo.opt_specified;
   return oinfo.opt_specified;
endfunction

function string vmm_opts::get_object_string(output bit is_set,
                                            input vmm_object obj,
                                            string name,
                                            string dflt,
                                            string doc = "",
                                            int verbosity = 0,
                                            string fname = "",
                                            int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_string called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::STR_ARGS, verbosity, doc, obj.get_object_hiername());
   if (oinfo.arg_specified) begin
     is_set = 1;
     return oinfo.sarg;
   end
   return dflt;
endfunction

function int    vmm_opts::get_object_int(output bit is_set,
                                         input vmm_object obj,
                                         string  name,
                                         int     dflt = 0,
                                         string  doc = "",
                                         int verbosity = 0,
                                         string fname = "",
                                         int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_int called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::INT_ARGS, verbosity, doc, obj.get_object_hiername());
   if (oinfo.arg_specified) begin
     is_set = 1;
     return oinfo.val;
   end
   return dflt;
endfunction

function void   vmm_opts::get_object_range(output bit is_set,
                                           input vmm_object obj,
                                           string  name,
                                           output int min, max,
                                           input  int dflt_min, dflt_max,
                                           string  doc  = "",
                                           int verbosity = 0,
                                           string fname = "",
                                           int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_range called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::RANGE_ARGS, verbosity, doc, obj.get_object_hiername());
   if (oinfo.arg_specified) begin
      min = oinfo.min;
      max = oinfo.max;
      return;
   end
   min = dflt_min;
   max = dflt_max;
endfunction

function vmm_object  vmm_opts::get_object_obj(output bit is_set,
                                              input vmm_object obj,
                                              string  name,
                                              vmm_object dflt = null,
                                              string fname = "",
                                              int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_obj called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::OBJ_ARGS, 0, "", obj.get_object_hiername());
   if (oinfo.arg_specified) begin
     is_set = 1;
     return oinfo.obj;
   end
   return dflt;
endfunction

function void   vmm_opts::set_bit(string  name,
                                  bit val,
                                  vmm_unit root = null,
                                  string fname = "",
                                  int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   split_hiername(name, var_name, hier);
   if (root != null)
     hier = {root.get_object_hiername(), ":", hier};
   val_str.itoa(val);
   oinfo = new(var_name, val_str);
   oinfo.opt_specified = 1;
   oinfo.pat_specified = 1;
   oinfo.src_type = vmm_opts_info::SV_FILE;
   oinfo.arg_type = vmm_opts_info::BOOL_ARGS;
   oinfo.arg_specified = 1;
   oinfo.val = val;
   oinfo.hier = hier;
   oinfo.fname = fname;
   oinfo.lineno = lineno;
   
   if (opts_info.exists(var_name)) begin
      oinfow = opts_info[var_name];
   end
   else begin
      oinfow = new(var_name, log);
      opts_info[var_name] = oinfow;
   end
   oinfow.add_option(oinfo);

endfunction

function void   vmm_opts::set_int(string  name,
                                  int val,
                                  vmm_unit root = null,
                                  string fname = "",
                                  int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
   val_str.itoa(val);
   oinfo = new(var_name, val_str);
   oinfo.opt_specified = 1;
   oinfo.pat_specified = 1;
   oinfo.src_type = vmm_opts_info::SV_FILE;
   oinfo.arg_type = vmm_opts_info::INT_ARGS;
   oinfo.arg_specified = 1;
   oinfo.val = val;
   oinfo.hier = hier;
   oinfo.fname = fname;
   oinfo.lineno = lineno;
   oinfo.regexp = vmm_path_match::compile_pattern({"@", hier}, log);
   
   if (opts_info.exists(var_name)) begin
      oinfow = opts_info[var_name];
   end
   else begin
      oinfow = new(var_name, log);
      opts_info[var_name] = oinfow;
   end
   oinfow.add_option(oinfo);

endfunction

function void   vmm_opts::set_string(string  name,
                                     string val,
                                     vmm_unit root = null,
                                     string fname = "",
                                     int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
   oinfo = new(var_name, val);
   oinfo.opt_specified = 1;
   oinfo.pat_specified = 1;
   oinfo.src_type = vmm_opts_info::SV_FILE;
   oinfo.arg_type = vmm_opts_info::STR_ARGS;
   oinfo.arg_specified = 1;
   oinfo.val = val;
   oinfo.hier = hier;
   oinfo.fname = fname;
   oinfo.lineno = lineno;
   oinfo.regexp = vmm_path_match::compile_pattern({"@", hier}, log);
   
   if (opts_info.exists(var_name)) begin
      oinfow = opts_info[var_name];
   end
   else begin
      oinfow = new(var_name, log);
      opts_info[var_name] = oinfow;
   end
   oinfow.add_option(oinfo);

endfunction

function void   vmm_opts::set_object(string  name,
                                     vmm_object obj,
                                     vmm_unit root = null,
                                     string fname = "",
                                     int lineno = 0);
   string var_name;
   string hier;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
   oinfo = new(var_name);
   oinfo.opt_specified = 1;
   oinfo.pat_specified = 1;
   oinfo.src_type = vmm_opts_info::SV_FILE;
   oinfo.arg_type = vmm_opts_info::OBJ_ARGS;
   oinfo.arg_specified = 1;
   oinfo.hier = hier;
   oinfo.obj = obj;
   oinfo.fname = fname;
   oinfo.lineno = lineno;
   oinfo.regexp = vmm_path_match::compile_pattern({"@", hier}, log);
   
   if (opts_info.exists(var_name)) begin
      oinfow = opts_info[var_name];
   end
   else begin
      oinfow = new(var_name, log);
      opts_info[var_name] = oinfow;
   end
   oinfow.add_option(oinfo);

endfunction

function void   vmm_opts::set_range(string  name,
                                    int min, max,
                                    vmm_unit root = null,
                                    string fname = "",
                                    int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
   val_str = `vmm_sformatf("[%0d:%0d]", min, max);
   oinfo = new(var_name, val_str);
   oinfo.opt_specified = 1;
   oinfo.pat_specified = 1;
   oinfo.src_type = vmm_opts_info::SV_FILE;
   oinfo.arg_type = vmm_opts_info::RANGE_ARGS;
   oinfo.arg_specified = 1;
   oinfo.min = min;
   oinfo.max = max;
   oinfo.hier = hier;
   oinfo.fname = fname;
   oinfo.lineno = lineno;
   oinfo.sarg = val_str;
   oinfo.regexp = vmm_path_match::compile_pattern({"@", hier}, log);
   
   if (opts_info.exists(var_name)) begin
      oinfow = opts_info[var_name];
   end
   else begin
      oinfow = new(var_name, log);
      opts_info[var_name] = oinfow;
   end
   oinfow.add_option(oinfo);

endfunction

function void vmm_opts::get_help(vmm_object root = null, int verbosity = 0);
   string usage[$];
   string unknown[$];
   `vmm_path_compiled comp_path;
   string exp_hier;
   int p;

   usage.push_back("VMM run-time options can be specified in the following formats:");
   usage.push_back("   1) +vmm_opts+<option1>+<option2>+<option3>+...");
   usage.push_back("   2) +vmm_<option1> +vmm_<option2> +vmm_<option3> ...");
   usage.push_back("   3) +<option1> +<option2> +<option3> ... in file(s)");
   usage.push_back("      specified using +vmm_opts_file+<fname1>+<fname2>+...");
   usage.push_back("   where <optionN> is <name>, <name>=<int> or <name>=<str>");
   usage.push_back(" ");

   comp_path = vmm_path_match::compile_path(log, root); 
   if (root != null) begin
     exp_hier = root.get_object_hiername();
     usage.push_back({"VMM run-time options defined by the hierarchy", exp_hier, " are:"});
   end
   else begin
     usage.push_back("VMM run-time options defined by this simulation are:");
   end 

   foreach (opts_info[name]) begin
      vmm_opts_info_wrapper optw = opts_info[name];
      foreach (optw.oinfo_q[i]) begin
         vmm_opts_info oinfo = optw.oinfo_q[i];
         if (oinfo.verbosity > verbosity) continue;
         if (root != null) begin
           if (! `vmm_str_match(oinfo.exp_hier, exp_hier)) begin
              continue;
           end
         end
         if (optw.is_used) begin
               usage.push_back(oinfo.help(++p, 1));
         end
         else begin
               unknown.push_back(oinfo.help(++p, 0));
         end
      end
   end

   if (log.start_msg(vmm_log::NOTE_TYP, vmm_log::NORMAL_SEV)) begin
      foreach (usage[i]) void'(log.text(usage[i]));
      log.end_msg();
   end

   if (unknown.size() > 0) begin
      string woops[$];
      woops.push_back("Following unknown VMM run-time options were specified:");
      foreach (unknown[i]) begin
         woops.push_back(unknown[i]);
      end
      if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
         foreach (woops[i]) void'(log.text(woops[i]));
         log.end_msg();
      end
  end
endfunction

function void vmm_opts::check_options_usage(int verbosity = 0);
   string woops[$];
   int p;
   woops.push_back("Following unknown VMM run-time options were specified:");
   foreach (opts_info[name]) begin
      vmm_opts_info_wrapper optw = opts_info[name];
      if (!optw.is_used) begin
         foreach (optw.oinfo_q[i]) begin
            vmm_opts_info oinfo = optw.oinfo_q[i];
            if (oinfo.verbosity > verbosity) continue;
            woops.push_back(oinfo.help(++p, 0));
         end
      end
   end
   if (woops.size() == 1) return;
   if (log.start_msg(vmm_log::FAILURE_TYP, vmm_log::WARNING_SEV)) begin
      foreach (woops[i]) void'(log.text(woops[i]));
      log.end_msg();
   end
endfunction

function bit vmm_opts::split(string line, output string argv[$]);
   string pre;
   string post;
   string tok[$];

   split = 1;
   
   if (line.len() == 0) return 0;
   post = line;
   forever begin
      if (`vmm_str_match(post, "[+]")) begin
         pre = `vmm_str_prematch(post);
         post = `vmm_str_postmatch(post);
         if (pre.len() != 0) begin
            // Only add the token if non-empty to strip leading blanks
            argv.push_back(pre);
         end
      end else begin
         //if no further matches, put in the last match if it's non-zero len
         if (post.len() > 0) begin
            argv.push_back(post);
         end
         break;
      end
   end
endfunction

function void vmm_opts::split_hiername(string pattern,
                                       output string name, 
                                       output string hier_pat);
   string one_char;
   string var_name;
   int len = pattern.len();
   for (int i=len-1; i>=0; i--) begin
      one_char = pattern.getc(i);
      if (one_char == ":") begin
        hier_pat = pattern.substr(0, i-1);
        name = var_name;
        return;
      end
      var_name = {one_char, var_name};
   end
   name = var_name;
endfunction

