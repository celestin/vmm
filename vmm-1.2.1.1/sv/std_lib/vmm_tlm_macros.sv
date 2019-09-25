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

// tlm macros

`define vmm_tlm_b_transport_export(SUFFIX) \
class vmm_tlm_b_transport_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data) extends vmm_tlm_export_base#(DATA); \
   static local vmm_object _obj; \
   local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0); \
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction: new \
\
   virtual task b_transport(int id = -1, DATA trans, ref int delay); \
      if(this.child_export == null)  \
         this.m_parent.b_transport``SUFFIX(id, trans, delay); \
      else \
         this.child_export.b_transport(id,trans,delay); \
   endtask : b_transport \
\
endclass : vmm_tlm_b_transport_export``SUFFIX

`define vmm_tlm_nb_transport_fw_export(SUFFIX) \
class vmm_tlm_nb_transport_fw_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE); \
\
   static local vmm_object _obj; \
   local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0); \
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds, ((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
      this.is_nb = 1; \
   endfunction: new \
\
   function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, ref PHASE ph, ref int delay); \
      if(this.child_export == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(id, trans, ph, delay); \
      else \
         nb_transport_fw = this.child_export.nb_transport_fw(id, trans, ph, delay); \
   endfunction : nb_transport_fw \
\
endclass : vmm_tlm_nb_transport_fw_export``SUFFIX

`define vmm_tlm_nb_transport_bw_export(SUFFIX) \
class vmm_tlm_nb_transport_bw_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_export_base#(DATA,PHASE); \
\
   static local vmm_object _obj; \
   local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0); \
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds, ((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
      this.is_nb = 1; \
   endfunction: new \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1); \
      if(this.child_export == null ) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(id, trans, ph, delay) ; \
      else \
         nb_transport_bw = this.child_export.nb_transport_bw(trans, ph, delay, id); \
   endfunction : nb_transport_bw \
\
endclass : vmm_tlm_nb_transport_bw_export``SUFFIX

`define vmm_tlm_analysis_export(SUFFIX) \
class vmm_tlm_analysis_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data ) extends vmm_tlm_analysis_export_base#(DATA); \
   static local vmm_object _obj; \
   local TARGET m_parent; \
\
   function  new(TARGET parent, string name , int max_binds = 1 , int min_binds = 0); \
      super.new( ($cast(_obj, parent)) ? _obj : null, name, max_binds, min_binds,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction : new  \
\
   virtual function void write(int id =-1, DATA trans); \
      if(this.child_export == null) \
         this.m_parent.write``SUFFIX(id, trans); \
      else \
         this.child_export.write(id,trans); \
   endfunction : write \
endclass : vmm_tlm_analysis_export``SUFFIX \


`define vmm_tlm_initiator_socket(SUFFIX) \
class vmm_tlm_initiator_socket``SUFFIX #(type INITIATOR = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_socket_base#(DATA,PHASE); \
\
   /* local */ static local vmm_object _obj; \
   /* local */ local INITIATOR m_parent; \
\
   function new(INITIATOR parent, string name); \
      super.new(($cast(_obj,parent))?_obj:null , name ,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction \
\
   virtual task b_transport(DATA trans, ref int delay); \
      if(this.parent_socket == null) \
         this.m_binding.b_transport(trans, delay); \
      else \
         this.parent_socket.b_transport(trans,delay); \
   endtask : b_transport \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans,  ref PHASE ph, ref int delay); \
      if(this.parent_socket == null) \
         nb_transport_fw = this.m_binding.nb_transport_fw(trans, ph ,delay); \
      else \
         nb_transport_fw = this.parent_socket.nb_transport_fw(trans, ph ,delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay); \
      if(this.child_socket == null) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(this.peer_id, trans, ph, delay); \
      else \
         nb_transport_bw = this.child_socket.nb_transport_bw(trans, ph, delay); \
   endfunction : nb_transport_bw \
\
endclass: vmm_tlm_initiator_socket``SUFFIX

`define vmm_tlm_target_socket(SUFFIX) \
class vmm_tlm_target_socket``SUFFIX#(type TARGET = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_socket_base#(DATA,PHASE); \
\
   /* local */ static local vmm_object _obj; \
   /* local */ local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);\
\
      super.new(($cast(_obj,parent))?_obj:null, name,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction: new \
\
   virtual task b_transport(DATA trans, ref int delay); \
      if(child_socket == null) \
         this.m_parent.b_transport``SUFFIX(this.peer_id , trans , delay ); \
      else \
         this.child_socket.b_transport(trans , delay ); \
   endtask : b_transport \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay); \
      if(child_socket == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(this.peer_id, trans,  ph ,delay); \
      else \
         nb_transport_fw = this.child_socket.nb_transport_fw(trans,  ph ,delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay); \
      if(parent_socket == null) \
         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph ,delay); \
      else \
         nb_transport_bw = this.parent_socket.nb_transport_bw(trans, ph ,delay); \
   endfunction : nb_transport_bw \
\
endclass: vmm_tlm_target_socket``SUFFIX

`define vmm_tlm_nb_transport_port(SUFFIX) \
class vmm_tlm_nb_transport_port``SUFFIX #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA, PHASE); \
   /* local */ static local vmm_object _obj; \
   //vmm_log log = new("vmm_tlm_nb_transport_port","class"); \
   local INITIATOR m_parent; \
   \
   function new(INITIATOR parent, string name); \
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ?_obj.get_log() : null); \
      this.is_nb = 1; \
      this.m_parent = parent; \
   endfunction: new \
   \
   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay); \
      if(this.parent_port == null) \
         nb_transport_fw = this.m_binding.nb_transport_fw(this.peer_id, trans,  ph, delay); \
      else \
         nb_transport_fw = this.parent_port.nb_transport_fw(trans,  ph, delay); \
   endfunction : nb_transport_fw \
   \
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1); \
      if(this.child_port == null ) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(id, trans, ph, delay); \
      else \
         nb_transport_bw = this.child_port.nb_transport_bw(trans, ph, delay, id); \
   endfunction : nb_transport_bw \
   \
endclass : vmm_tlm_nb_transport_port``SUFFIX


`define vmm_tlm_nb_transport_export(SUFFIX) \
class vmm_tlm_nb_transport_export``SUFFIX #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE); \
   /* local */ static local vmm_object _obj; \
   //vmm_log log = new("vmm_tlm_nb_transport_export","class"); \
   local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0); \
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds ,((parent != null) && $cast(_obj, parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
      this.is_nb = 1; \
   endfunction: new \
\
   function vmm_tlm::sync_e nb_transport_fw(int id = 1, DATA trans,  ref PHASE ph, ref int delay); \
      if(this.child_export == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(id, trans, ph, delay); \
      else \
         nb_transport_fw = this.child_export.nb_transport_fw(id, trans, ph, delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1); \
      int q[$]; \
      if(this.parent_export == null ) \
      begin \
         if(id < 0) \
         begin \
            q = this.bindings_id.find_first_index(x) with (x!=null); \
            nb_transport_bw = this.bindings_id[q[0]].nb_transport_bw(trans, ph, delay, id); \
         end \
         else \
            nb_transport_bw = this.bindings_id[id].nb_transport_bw(trans, ph, delay, id); \
      end \
      else \
         nb_transport_bw = this.parent_export.nb_transport_bw(trans, ph, delay, id); \
   endfunction : nb_transport_bw \
\
endclass : vmm_tlm_nb_transport_export``SUFFIX

