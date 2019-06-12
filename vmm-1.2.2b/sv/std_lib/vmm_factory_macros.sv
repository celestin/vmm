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

`define vmm_class_factory(classname) \
 \
  typedef vmm_class_factory_base#(classname) _factory_base; \
 \
  static function Xadd_patternX(vmm_factory_pattern_info#(classname) fact); \
     _factory_base::XpatternXQ.push_front(fact); \
  endfunction \
 \
  static function classname this_type(); \
     bit flg; \
     return _factory_base::Xfactory_typeX(flg); \
  endfunction \
 \
  static function classname create_instance(vmm_object parent, \
                                            string name, \
                                            string fname = `"`", \
                                            int lineno   = 0); \
     return _factory_base::create_instance(parent, name, fname, lineno); \
  endfunction \
 \
  static function void override_with_new(string name,  \
                                     classname factory, \
                                     vmm_log log, \
                                     string fname = "", \
                                     int lineno   = 0); \
     _factory_base::override_with_new(name, factory, log, fname, lineno); \
  endfunction \
 \
  static function void override_with_copy(string name,  \
                                      classname factory, \
                                      vmm_log log, \
                                      string fname = "", \
                                      int lineno   = 0); \
     _factory_base::override_with_copy(name, factory, log, fname, lineno); \
  endfunction \


