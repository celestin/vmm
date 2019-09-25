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

//VMM unit configuration macros
`define vmm_unit_config_begin(_classname) \
   virtual function void configure_ph();

`define vmm_unit_config_end(_classname) \
   endfunction


`define vmm_unit_config_rand_boolean(_name, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     _name = vmm_opts::get_object_bit(is_set, this, `"_name`", _descr, _verbosity, `__FILE__, `__LINE__); \
     if (is_set) _name.rand_mode(0); \
  end

`define vmm_unit_config_rand_int(_name, dflt, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     _name = vmm_opts::get_object_int(is_set, this, `"_name`", dflt, _descr, _verbosity, `__FILE__, `__LINE__); \
     if (is_set) _name.rand_mode(0); \
  end

`define vmm_unit_config_rand_obj(_name, dflt, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     $cast(_name, vmm_opts::get_object_obj(is_set, this, `"_name`", dflt, _descr, _verbosity, `__FILE__, `__LINE__)); \
     if (is_set) _name.rand_mode(0); \
  end

`define vmm_unit_config_boolean(_name, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     _name = vmm_opts::get_object_bit(is_set, this, `"_name`", _descr, _verbosity, `__FILE__, `__LINE__); \
  end

`define vmm_unit_config_int(_name, dflt, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     _name = vmm_opts::get_object_int(is_set, this, `"_name`", dflt, _descr, _verbosity, `__FILE__, `__LINE__); \
  end

`define vmm_unit_config_obj(_name, dflt, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     $cast(_name, vmm_opts::get_object_obj(is_set, this, `"_name`", dflt, _descr, _verbosity, `__FILE__, `__LINE__)); \
  end


`define vmm_unit_config_string(_name, dflt, _descr, _verbosity, _attr) \
  begin \
     bit is_set; \
     _name = vmm_opts::get_object_string(is_set, this, `"_name`", dflt, _descr, _verbosity, `__FILE__, `__LINE__); \
  end


