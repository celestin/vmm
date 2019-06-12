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

class rtl_config_file_format extends vmm_rtl_config_file_format;

  virtual function bit fopen(vmm_rtl_config cfg, 
                             string mode, 
                             string fname = "", 
                             int lineno = 0);
    string filename = {cfg.prefix, ":", cfg.get_object_hiername(), ".rtl_conf"};
    vmm_rtl_config::file_ptr = $fopen(filename, mode);
    if (vmm_rtl_config::file_ptr == 0) return 0;
    else return 1;
  endfunction

  function string get_val(string str);
    if (`vmm_str_match(str, "     : ")) begin
       string fname = `vmm_str_prematch(str);
       string fval = `vmm_str_postmatch(str);
       if (`vmm_str_match(fval, ";")) begin
         fval = `vmm_str_prematch(fval);
       end
       return fval;
    end
  endfunction

  virtual function bit read_bit(string name, output bit value);
    int r;
    string str;
    r = $freadstr(str, vmm_rtl_config::file_ptr);
    str = get_val(str);
    value = str.atoi();
    $display("Got %b for %s", value, name);
    return (r != 0);
  endfunction

  virtual function bit read_int(string name, output int value);
    int r;
    string str;
    $display("Calling read_int for %s", name);
    r = $freadstr(str, vmm_rtl_config::file_ptr);
    str = get_val(str);
    value = str.atoi();
    $display("Got %0d for %s", value, name);
    return (r != 0);
  endfunction

  virtual function bit read_string(string name, output string value);
    int r;
    string str;
    $display("Calling read_string for %s", name);
    r = $freadstr(str, vmm_rtl_config::file_ptr);
    value = get_val(str);
    $display("Got %s for %s", value, name);
    return (r != 0);
  endfunction

  virtual function bit write_bit(string name, bit value);
    $fwrite(vmm_rtl_config::file_ptr, "%s     : %b;\n", name, value);
    return 1;
  endfunction

  virtual function bit write_int(string name, int value);
    $fwrite(vmm_rtl_config::file_ptr, "%s     : %0d;\n", name, value);
    return 1;
  endfunction

  virtual function bit write_string(string name, string value);
    $fwrite(vmm_rtl_config::file_ptr, "%s     : %s;\n", name, value);
    return 1;
  endfunction

  virtual function void fclose();
    $fclose(vmm_rtl_config::file_ptr);
  endfunction

endclass

