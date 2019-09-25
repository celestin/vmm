
// tlm macros

`define vmm_tlm_b_transport_export(SUFFIX) \
class vmm_tlm_b_transport_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm) extends vmm_tlm_export_base#(DATA,PHASE); \
   static local vmm_object _obj; \
   local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0); \
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction: new \
\
   virtual task b_transport(int id = -1, DATA trans, PHASE ph = null , input int delay = -1); \
      if(this.child_export == null)  \
         this.m_parent.b_transport``SUFFIX(id, trans, ph , delay); \
      else \
         this.child_export.b_transport(id,trans, ph ,delay); \
   endtask : b_transport \
\
endclass : vmm_tlm_b_transport_export``SUFFIX

`define vmm_tlm_nb_transport_fw_export(SUFFIX) \
class vmm_tlm_nb_transport_fw_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm ) extends vmm_tlm_export_base#(DATA, PHASE); \
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
   function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, PHASE ph = null, int delay = -1); \
      if(this.child_export == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(id, trans, ph, delay); \
      else \
         nb_transport_fw = this.child_export.nb_transport_fw(id, trans, ph, delay); \
   endfunction : nb_transport_fw \
\
endclass : vmm_tlm_nb_transport_fw_export``SUFFIX

`define vmm_tlm_nb_transport_bw_export(SUFFIX) \
class vmm_tlm_nb_transport_bw_export``SUFFIX #(type TARGET = vmm_xactor, type DATA = vmm_data , type PHASE = vmm_tlm) extends vmm_tlm_export_base#(DATA,PHASE); \
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
   function vmm_tlm::sync_e nb_transport_bw(int id = -1, DATA trans, PHASE ph = null, int delay = -1); \
      if(this.child_export == null ) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(id, trans, ph, delay) ; \
      else \
         nb_transport_bw = this.child_export.nb_transport_bw(id, trans, ph, delay); \
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


`define vmm_tlm_simple_initiator_socket(SUFFIX) \
class vmm_tlm_simple_initiator_socket``SUFFIX #(type INITIATOR = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm) extends vmm_tlm_socket_base#(DATA,PHASE); \
\
   /* local */ static local vmm_object _obj; \
   /* local */ local INITIATOR m_parent; \
\
   function new(INITIATOR parent, string name); \
      super.new(($cast(_obj,parent))?_obj:null , name ,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction \
\
   virtual task b_transport(DATA trans, PHASE ph = null , input int delay = -1); \
      if(this.parent_socket == null) \
         this.m_binding.b_transport(trans, ph , delay); \
      else \
         this.parent_socket.b_transport(trans, ph ,delay); \
   endtask : b_transport \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans,  PHASE ph = null, int delay = -1); \
      if(this.parent_socket == null) \
         nb_transport_fw = this.m_binding.nb_transport_fw(trans, ph ,delay); \
      else \
         nb_transport_fw = this.parent_socket.nb_transport_fw(trans, ph ,delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, PHASE ph = null, int delay = -1); \
      if(this.child_socket == null) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(this.peer_id, trans, ph, delay); \
      else \
         nb_transport_bw = this.child_socket.nb_transport_bw(trans, ph, delay); \
   endfunction : nb_transport_bw \
\
endclass: vmm_tlm_simple_initiator_socket``SUFFIX

`define vmm_tlm_simple_target_socket(SUFFIX) \
class vmm_tlm_simple_target_socket``SUFFIX#(type TARGET = vmm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm) extends vmm_tlm_socket_base#(DATA,PHASE); \
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
   virtual task b_transport(DATA trans, PHASE ph = null , int delay = -1); \
      if(child_socket == null) \
         this.m_parent.b_transport``SUFFIX(this.peer_id , trans , ph , delay ); \
      else \
         this.child_socket.b_transport(trans , ph , delay ); \
   endtask : b_transport \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans, PHASE ph = null, int delay = -1); \
      if(child_socket == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(this.peer_id, trans,  ph ,delay); \
      else \
         nb_transport_fw = this.child_socket.nb_transport_fw(trans,  ph ,delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, PHASE ph = null, int delay = -1); \
      if(parent_socket == null) \
         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph ,delay); \
      else \
         nb_transport_bw = this.parent_socket.nb_transport_bw(trans, ph ,delay); \
   endfunction : nb_transport_bw \
\
endclass: vmm_tlm_simple_target_socket``SUFFIX

`define vmm_tlm_nb_transport_port(SUFFIX) \
class vmm_tlm_nb_transport_port``SUFFIX#(type INITIATOR = vmm_xactor, type DATA = vmm_data, type FW_PHASE = vmm_tlm, type BW_PHASE = FW_PHASE) extends vmm_tlm_socket_base#(DATA,FW_PHASE); \
   /* local */ static local vmm_object _obj; \
   /* local */ local INITIATOR m_parent; \
   function new(INITIATOR parent, string name); \
      super.new(($cast(_obj,parent))?_obj:null , name,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans, FW_PHASE ph = null, int delay = -1); \
      if(parent_socket == null) \
         nb_transport_fw = this.m_binding.nb_transport_fw(trans, ph, delay); \
      else \
         nb_transport_fw = this.parent_socket.nb_transport_fw(trans, ph, delay); \
   endfunction : nb_transport_fw \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, BW_PHASE ph = null, int delay = -1); \
      if(child_socket == null) \
         nb_transport_bw = this.m_parent.nb_transport_bw``SUFFIX(this.peer_id, trans, ph, delay); \
      else \
         nb_transport_bw = this.child_socket.nb_transport_bw( trans, ph, delay); \
   endfunction : nb_transport_bw \
\
endclass: vmm_tlm_nb_transport_port``SUFFIX

`define vmm_tlm_nb_transport_export(SUFFIX) \
class vmm_tlm_nb_transport_export``SUFFIX#(type TARGET = vmm_xactor, type DATA = vmm_data, type FW_PHASE = vmm_tlm, type BW_PHASE = FW_PHASE) extends vmm_tlm_socket_base#(DATA,BW_PHASE); \
   /* local */ static local vmm_object _obj; \
   /* local */ local TARGET m_parent; \
\
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);\
      super.new(($cast(_obj,parent))?_obj:null, name,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); \
      this.m_parent = parent; \
   endfunction: new \
\
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, BW_PHASE ph = null, int delay = -1); \
      if(parent_socket == null) \
         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph, delay); \
      else \
         nb_transport_bw = this.parent_socket.nb_transport_bw(trans, ph, delay); \
   endfunction : nb_transport_bw \
\
   function vmm_tlm::sync_e nb_transport_fw(DATA trans, FW_PHASE ph = null, int delay = -1); \
      if(child_socket == null) \
         nb_transport_fw = this.m_parent.nb_transport_fw``SUFFIX(this.peer_id, trans, ph, delay); \
      else \
         nb_transport_fw = this.child_socket.nb_transport_fw(trans, ph, delay); \
   endfunction : nb_transport_fw \
\
endclass: vmm_tlm_nb_transport_export``SUFFIX

