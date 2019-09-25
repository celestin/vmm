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
            string args;
            case (arg_type)
              BOOL_ARGS:  args = "boolean ( No Argument )";
              STR_ARGS: args = "string";
              INT_ARGS: args = "int";
              RANGE_ARGS: args = "int range [ min:max ]";
            endcase
            $sformat(fmt, "|%d| NAME     : %s\n|    | ARG TYPE : %s\n|    | INFO     : %s\n|    | DESCR    : %s", id, opt, args, txt, doc );
         end
         else begin //option is needed but ignored due to lesser priority
            $sformat(fmt, "|%d| NAME     : %s\n|    | INFO     : %s (Ignored)\n|    | DESCR    : %s", id, opt, txt, doc );
         end
      end
      else begin
         $sformat(fmt, "|%d| NAME : %s\n|    | INFO     : %s (Not Used Anywhere So far)\n|    | DESCR    : %s", id, opt, txt, doc);
      end
      if ( id == 1)
        fmt = `vmm_sformatf("-------------------------------------------------------------------\n", fmt, 
                          "\n-------------------------------------------------------------------");
      else
        fmt = `vmm_sformatf(fmt, "\n-------------------------------------------------------------------");
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
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
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
       foreach (oinfo_q[i]) begin
          if (hier == oinfo_q[i].hier) begin
             oinfo = oinfo_q[i];
             oinfo.exp_hier = hier;
             oinfo.is_expected = 1;
             get_option =  oinfo;
             is_used = 1;
             return;
          end
       end
       oinfo = new(this.name); 
       oinfo_q.push_back(oinfo);
     end
     oinfo.exp_hier = hier;
     oinfo.is_expected = 1;
     get_option =  oinfo;
     is_used = 1; 
   endfunction

   local function vmm_opts_info get_opts_from_type(vmm_opts_info::src_type_e src_type, string hier);
      vmm_opts_info match_opts[$];
      vmm_opts_info src_match_opts[$];
      vmm_opts_info result;

      match_opts = oinfo_q.find(idx) with ( idx.src_type == src_type && idx.opt_specified );
      foreach (match_opts[i]) begin
        `vmm_path_compiled comp_path;
        if (match_opts[i].hier == "") return match_opts[i];
        if (match_opts[i].pat_specified) begin //hierarchical option
           if (match_opts[i].hier == hier) return match_opts[i];
           comp_path = vmm_path_match::compile_path(log, null, hier);
           if (vmm_path_match::match(comp_path, match_opts[i].regexp)) begin
             `vmm_verbose(log, `vmm_sformatf("Path %s and Pattern %s matching.. ", hier, match_opts[i].hier));
             if (src_type != vmm_opts_info::SV_FILE) return match_opts[i];
             else begin
               vmm_test t;
               `ifndef NO_VMM12_PHASING
               if ($cast(t, match_opts[i].root)) return match_opts[i];
               `endif
               src_match_opts.push_back(match_opts[i]);
             end
           end
           else begin
             `vmm_verbose(log, `vmm_sformatf("Path %s and Pattern %s NOT matching", hier, match_opts[i].hier));
           end
        end
      end
      foreach (src_match_opts[i]) begin
         string str1, str2;
         if (result == null) begin
            result = src_match_opts[i];
            continue;
         end
        `ifndef NO_VMM12_PHASING
         if (src_match_opts[i].root == null) return src_match_opts[i];
         if (result.root == null) return result;
         str1 = result.root.get_object_hiername();
         str2 = src_match_opts[i].root.get_object_hiername();
         if (str1.len() > str2.len()) begin
           result = src_match_opts[i];
         end
         `endif
      end
      return result;
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
              string onec ;
			  onec = `_TO_CAST_TO_STRING(t_str.getc(i));
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
function vmm_opts_info vmm_opts::send_opts(string name, vmm_opts_info::arg_type_e arg_type, int verbosity, string doc, string hier = "");
    vmm_opts_info oinfo;
    oinfo = vmm_opts::get_opts_by_name(name, arg_type, verbosity, doc, hier);
    return oinfo;  
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
   if (arg_type == vmm_opts_info::REAL_ARGS) oinfo.r = oinfo.sarg.atoreal();
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

// //////////////////////////////////////////// 
// Class: vmm_opts
// 
// Utility class that provides the facility to pass values from the command line during 
// runtime, or from the source code, across hierarchies.
//    
// Function: get_bit 
// 
// Displays the known options used by the verification environment with the specified
// vmm_object hierarchy, with verbosity lower than or equal to the absolute value of the
// specified verbosity. If no vmm_unit root is specified, the options used by all object
// hierarchies are displayed. A verbosity value must be within the range -10 to 10. If the
// specified verbosity value is negative, the hierarchical name of each vmm_unit instance
// that uses an option is also displayed. 
// 
function bit    vmm_opts::get_bit(string name,
                                  string doc = "",
                                  int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::BOOL_ARGS, verbosity, doc);
   return oinfo.opt_specified;
endfunction

// //////////////////////////////////////////// 
// Function: get_string 
// 
// Returns string value, if the argument name and its string value are specified on the
// command-line. Otherwise, it returns the default value specified in the dflt argument.
// The option is specified using the command line +<vmm_name=value or +vmm_opts+name=value.
// You can specify a description of the option using doc, and the verbosity level of the
// option using verbosity. A verbosity value must be within the range 0 to 10. The fname
// and lineno arguments are used to track the file name and the line number, where the option
// is specified. These optional arguments are used to providing information through
// the get_help> method. 
// 
//|   string str;
//|   str = vmm_opts :: get_string ("FOO", "DEF", 
//|      "str value from command line");
//|   
//|   Command line:
//|   simv +vmm_FOO=HELLO or simv +vmm_opts+FOO=HELLO 
function string vmm_opts::get_string(string name,
                                     string dflt="",
                                     string doc = "",
                                     int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::STR_ARGS, verbosity, doc);
   if (oinfo.arg_specified) return oinfo.sarg;
   return dflt;
endfunction

// //////////////////////////////////////////// 
// Function: get_int 
// 
// Returns an integer value, if the argument name and its integer value are specified on
// the command line. Otherwise, returns the default value specified in the dflt argument.
// The option is specified using the command line +<vmm_name=value or +vmm_opts+name=value.
// You can specify a description of the option using doc, and the verbosity level of the
// option using verbosity. A verbosity value must be within the range 0 to 10. The fname
// and lineno arguments are used to track the file name and the line number, where the option
// is specified. These optional arguments are used to provide information through the
// get_help> method. 
// 
//|   int i;
//|   i = get_int ("FOO", 0, 
//|      "Value set for 'i' from command line");
//|   
//|   Command line:
//|   simv +vmm_FOO=100 or simv +vmm_opts+FOO=100
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

function real    vmm_opts::get_real(string  name,
                                  real     dflt = 0,
                                  string  doc = "",
                                  int verbosity = 0,
                                  string fname = "",
                                  int lineno = 0);
   vmm_opts_info oinfo;

   oinfo = get_opts_by_name(name, vmm_opts_info::REAL_ARGS, verbosity, doc);
   if (oinfo.arg_specified) return oinfo.r;

   return dflt;
endfunction

// //////////////////////////////////////////// 
// Function: get_range 
// 
// Returns the named integer range option. A range option is specified using the syntax
// +<vmm_name=[min:max] or +vmm_opts+name=[min:max]. You can specify a description
// of the option using doc, and the verbosity level of the option using verbosity. A verbosity
// value must be within the range 0 to 10. The fname and lineno arguments are used to track
// the file name and the line number, where the option is specified. These optional arguments
// are used to provide information through the get_help> method. 
// If no explicit values are provided for integer range of the specified hierarchy, sets
// the default range values to specified arguments dflt_min & dflt_max to the min and max
// arguments respectively. The fname and lineno arguments are used to track the file name
// and the line number where the get_object_range is invoked. 
// 
//|   int min_val;
//|   int max_val;
//|   
//|   get_range("FOO", min_val, max_val, 
//|      -1, -1, "SET range", 0);
//|   
//|   Command line:
//|   simv +vmm_FOO=[5:10] or simv +vmm_opts+FOO=[5:10]
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

// //////////////////////////////////////////// 
// Function: get_obj 
// 
// If an explicit value is specified, returns the globally named object type option and
// sets the is_set argument to true. If no object matches the expression specified by name,
// returns the default object specified by argument dflt.Object type options can only
// be set using the <set_object> method. The fname and lineno arguments can
// be used to track the file name and the line number where the get_obj is invoked from. 
// 
//|   class A extends vmm_object;
//|   endclass
//|   
//|   initial begin
//|      A a = new ("a");
//|      vmm_object obj;
//|      bit is_set;
//|      obj = vmm_opts :: get_obj(is_set, "OBJ", a);
//|   end
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

// //////////////////////////////////////////// 
// Function: get_object_bit 
// 
// If an explicit value is specified, returns the named boolean type option for the specified
// object instance, and sets the is_set argument to true. You can specify a description
// of the option using doc, and the verbosity level of the option using verbosity. The verbosity
// value must be within the range 0 to 10, with 10 being the highest. The fname and lineno
// arguments are used to track the file name and the line number, where the option is specified.
// These optional arguments are used to provide information to the user through the <get_help>
// method. 
// 
//|   class B extends vmm_object;
//|      bit foo, is_set;
//|      function new(string name, vmm_object parent=null);
//|      foo = get_object_bit(is_set, this, "FOO", 
//|         "SET foo value", 0);
//|      endfunction
//|   endclass
//|   
//|   Command line:
//|   simv +vmm_FOO@A:%:b
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

// //////////////////////////////////////////// 
// Function: get_object_string 
// 
// If an explicit value is specified, returns the named string type option for the specified
// object instance, and sets the is_set argument to true. If no explicit value is specified,
// specified default string name dftl is assigned to string name. You can specify a description
// of the option using doc, and the verbosity level of the option using verbosity. The verbosity
// value must be within the range 0 to 10. The fname and lineno arguments are used to track
// the file name and the line number, where the option is specified. These optional arguments
// are used to provide information through the <get_help> method. The fname
// and lineno arguments are used to track the file name and the line number where the get_object_string
// is invoked. 
// 
//|   class B extends vmm_object;
//|      string foo="ZERO";
//|      function new(string name, vmm_object parent=null);
//|         bit is_set;
//|         super.new(parent,name);
//|         foo = get_object_string(is_set, this, 
//|            "FOO", "DEF_VAL", "SET foo value", 0);
//|      endfunction
//|   endclass 
//|   
//|   Command line:
//|   simv +vmm_FOO=HELLO@%:X:b
function string vmm_opts::get_object_string(output bit is_set,
                                            input vmm_object obj,
                                            string name,
                                            string dflt="",
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

// //////////////////////////////////////////// 
// Function: get_object_int 
// 
// If an explicit value is specified, returns the named integer type option for the specified
// object instance and sets the is_set argument to true. You can specify a description
// of the option using doc, and the verbosity level of the option using verbosity. The verbosity
// value must be within the range 0 to 10. The fname and lineno arguments are used to track
// the file name and the line number, where the option is specified. These optional arguments
// are used to provide information through the <get_help> method. 
// 
//|   class B extends vmm_object;
//|      int foo;
//|      function new(string name, vmm_object parent=null);
//|         bit is_set;
//|         super.new(parent,name);
//|         foo = get_object_int(is_set, this, "FOO", 
//|            2, "SET foo value", 0);
//|      endfunction
//|   endclass
//|   
//|   Command line:
//|   simv +vmm_FOO=25@%:X:b
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

// //////////////////////////////////////////// 
// Function: get_object_range 
// 
// If an explicit range is specified, sets the min and max parameters to the values of the
// named integer-range-type option for the specified object instance, and sets the is_set
// argument to true. A range option is specified using the syntax +<vmm_name=[min:max].
// You can specify a description of the option using doc, and the verbosity level of the
// option using verbosity. A verbosity value must be within the range 0 to 10. The fname
// and lineno arguments are used to track the file name and the line number, where the option
// is specified. These optional arguments are used to provide information through the
// get_help> method. 
// If no explicit values are provided for integer range of the specified hierarchy, sets
// the default range values to specified arguments dflt_min & dflt_max to the min and max
// arguments respectively. The fname and lineno arguments are used to track the file name
// and the line number where the get_object_range is invoked. 
// 
//|   class B extends vmm_object;
//|      int min_val = -1;
//|      int max_val = -1;
//|      function new(string name, vmm_object parent=null);
//|         bit is_set;
//|         super.new(parent,name);
//|         get_object_range(is_set, this, 
//|         "FOO", min_val, max_val,-1,-1, "SET foo value", 0);
//|      endfunction  
//|   endclass
//|   
//|   Command line:
//|   simv +vmm_FOO=[5:10]@%:X:b
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

// //////////////////////////////////////////// 
// Function: get_object_obj 
// 
// Iif an explicit value is specified, returns the named object type option for the specified
// object instance and set the is_set argument to true. If no object matches the expression
// specified by name, returns the default object specified by argument dflt. You can specify
// a description of the option using doc, and the verbosity level of the option using verbosity.
// Object type options can only be set using the <set_object> method. The fname
// and lineno arguments can be used to track the file name and the line number where the get_object_obj
// is invoked from. 
// 
//|   class A extends vmm_object;
//|      int foo = 11;
//|      function new( vmm_object parent=null, string name);
//|         super.new(parent, name);
//|      endfunction
//|   endclass
//|   
//|   class B extends vmm_object;
//|      A a1, a2;
//|      function new(vmm_object parent=null, string name);
//|         bit is_set;
//|         super.new(parent, name);
//|         a1 = new(null, "a1");
//|         a2 = new(null, "a2");
//|         a2.foo = 22;
//|         $cast(a1, get_object_obj(is_set, this, 
//|            "OBJ_F1",a2,"SET OBJ", 0));
//|      endfunction
//|   endclass
function vmm_object  vmm_opts::get_object_obj(output bit is_set,
                                              input vmm_object obj,
                                              string  name,
                                              vmm_object dflt = null,
                                              string  doc  = "",
                                              int verbosity = 0,
                                              string fname = "",
                                              int lineno = 0);
   vmm_opts_info oinfo;

   if (obj == null)
     `vmm_fatal(log, {"get_object_obj called with null object for option", name});
   oinfo = get_opts_by_name(name, vmm_opts_info::OBJ_ARGS, verbosity, doc, obj.get_object_hiername());
   if (oinfo.arg_specified) begin
     is_set = 1;
     return oinfo.obj;
   end
   return dflt;
endfunction

// //////////////////////////////////////////// 
// Function: set_bit 
// 
// Sets the hierarchically named boolean type option for the specified <vmm_object instances
// as specified by val. If no vmm_unit root is specified, the hierarchical option name
// is assumed to be absolute. The argument name can be a pattern. When get_object_bit>
// is called in any object whose hierarchical name matches the pattern, the option is set
// for that boolean variable. The fname and lineno arguments are used to track the file
// name and the line number, where the option is specified from. 
// 
//|   class B extends vmm_object;
//|      bit foo;
//|      function new(string name, vmm_object parent=null);
//|         bit is_set;
//|         super.new(parent,name);
//|         foo = get_object_bit(is_set, this, "FOO",
//|            "SET foo value", 0);
//|      endfunction
//|   endclass
//|   
//|   B b2;
//|   initial begin
//|      set_bit("b2:FOO",null);
//|      b2 = new("b2", null);
//|   end
function void   vmm_opts::set_bit(string  name,
                                  bit val,
      `ifndef NO_VMM12_PHASING
                                  vmm_unit root = null,
      `endif
                                  string fname = "",
                                  int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   split_hiername(name, var_name, hier);
      `ifndef NO_VMM12_PHASING
   if (root != null)
     hier = {root.get_object_hiername(), ":", hier};
      `endif
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

// //////////////////////////////////////////// 
// Function: set_int 
// 
// Sets the hierarchically named integer type option for the specified <vmm_object instances
// as specified by val. If no vmm_unit root is specified, the hierarchical option name
// is assumed to be absolute. The argument name can be a pattern. When get_object_bit>
// is called in any object whose hierarchical name matches the pattern, the option is set
// for that integer variable. The fname and lineno arguments are used to track the file
// name and the line number, where the option is specified from. 
// 
//|   class A extends vmm_object;
//|      int a_foo;
//|      function new(vmm_object parent=null, string name);
//|         bit is_set;
//|         super.new(parent, name);
//|         a_foo = get_object_int(is_set, this, 
//|            "A_FOO", 2 , "SET a_foo value", 0);
//|      endfunction
//|   endclass
//|   
//|   class D extends vmm_object;
//|      A a1;
//|      ...
//|   endclass
//|   
//|   initial  begin
//|      D d2;
//|      set_int("d2:a1:A_FOO", 99,null);
//|      d2 = new (null, "d2");
//|   end
function void   vmm_opts::set_int(string  name,
                                  int val,
      `ifndef NO_VMM12_PHASING
                                  vmm_unit root = null,
      `endif
                                  string fname = "",
                                  int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
      `ifndef NO_VMM12_PHASING
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
      `endif
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
      `ifndef NO_VMM12_PHASING
                                     vmm_unit root = null,
      `endif
                                     string fname = "",
                                     int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
      `ifndef NO_VMM12_PHASING
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
      `endif
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

// //////////////////////////////////////////// 
// Function: set_object 
// 
// Sets the hierarchically named type-specific option for the specified <vmm_object
// instances. If no vmm_unit root is specified, the hierarchical option name is assumed
// to be absolute. When called from the vmm_unit::configure_ph> method, the root unit
// must always be specified as this, because vmm_unit instances can only configure lower-level
// instances during the configure phase. The hierarchical option name is specified by
// prefixing the option name with a hierarchical vmm_unit name and a colon (:). 
// The hierarchical option name may be specified using a match pattern or a regular expression,
// except for the last part of the hierarchical name (the name of the option itself). The
// hierarchical option name may specify a namespace. An error is reported, if the option
// value is not eventually used. 
// The fname and lineno arguments are used to track the file name and the line number, where
// the option is specified from. 
// 
//|   class A extends vmm_object;
//|      int foo = 11;
//|      function new( vmm_object parent=null, string name);
//|         bit is_set;
//|         super.new(parent, name);
//|      endfunction
//|   endclass
//|   
//|   class B extends vmm_object;
//|      A a1;
//|      A a2;
//|      function new(vmm_object parent=null, string name);
//|         bit is_set;
//|         super.new(parent, name);
//|         a1 = new(null, "a1");
//|         a2 = new(null, "a2");
//|         a2.foo = 22;
//|         $cast(a1, get_object_obj(is_set, this, 
//|            "OBJ_F1",a2,"SET OBJ", 0));
//|      endfunction
//|   endclass
//|   
//|   B b2;
//|   A a3;
//|   initial begin
//|      a3 = new(null, "a3");
//|      a3.foo = 99;
//|      set_object("b2:OBJ_F1", a3,null,,);
//|      b2 = new(null, "b2");	
//|   end
function void   vmm_opts::set_object(string  name,
                                     vmm_object obj,
      `ifndef NO_VMM12_PHASING
                                     vmm_unit root = null,
      `endif
                                     string fname = "",
                                     int lineno = 0);
   string var_name;
   string hier;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
      `ifndef NO_VMM12_PHASING
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
      `endif
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

// //////////////////////////////////////////// 
// Function: set_range 
// 
// Sets the hierarchically named integer range type option, for the specified <vmm_object
// instances. If no vmm_unit root is specified, then the hierarchical option name is assumed
// to be absolute. The name argument can be a pattern. When get_object_range>
// is called in an object whose hierarchical name matches the pattern, then min and max
// are returned. 
// The fname and lineno arguments are used to track the file name and the line number, where
// the range is specified from. 
// 
//|   class B extends vmm_object;
//|      int min_val = -1;
//|      int max_val = -1;
//|      function new(string name, vmm_object parent=null);
//|         bit is_set;
//|         super.new(parent,name);
//|         get_object_range(is_set, this, 
//|            "FOO",min_val, max_val, -1,-1, "SET foo value", 0);
//|      endfunction
//|   endclass
//|   initial begin
//|      B b2;
//|      set_range("b2:FOO", 1, 99, null);
//|      b2 = new("b2", null);
//|   end
function void   vmm_opts::set_range(string  name,
                                    int min, max,
      `ifndef NO_VMM12_PHASING
                                    vmm_unit root = null,
      `endif
                                    string fname = "",
                                    int lineno = 0);
   string var_name;
   string hier;
   string val_str;
   vmm_opts_info oinfo;
   vmm_opts_info_wrapper oinfow;

   if (name.getc(0) == "@") name = name.substr(1, name.len()-1);
   split_hiername(name, var_name, hier);
      `ifndef NO_VMM12_PHASING
   if (root != null)
      hier = {root.get_object_hiername(), ":", hier};
      `endif
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

   if(root == null)
      comp_path = vmm_path_match::compile_path(log, null,"^"); 
   else
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
      one_char = `_TO_CAST_TO_STRING(pattern.getc(i));
      if (one_char == ":") begin
        hier_pat = pattern.substr(0, i-1);
        name = var_name;
        return;
      end
      var_name = {one_char, var_name};
   end
   name = var_name;
endfunction

