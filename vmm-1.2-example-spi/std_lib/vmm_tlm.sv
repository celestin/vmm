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
class vmm_tlm;
   typedef enum {TLM_REFUSED, 
                 TLM_ACCEPTED, 
                 TLM_UPDATED, 
                 TLM_COMPLETED 
                 } sync_e;

   typedef enum {BEGIN_REQ,
                 END_REQ,
                 BEGIN_RESP,
                 END_RESP
                 } phase_e;

   typedef enum {TLM_BLOCKING_PORT, 
                 TLM_BLOCKING_EXPORT, 
                 TLM_NONBLOCKING_FW_PORT, 
                 TLM_NONBLOCKING_FW_EXPORT, 
                 TLM_NONBLOCKING_PORT, 
                 TLM_NONBLOCKING_EXPORT, 
                 TLM_ANALYSIS_PORT, 
                 TLM_ANALYSIS_EXPORT
                 } intf_e;

   sync_e sync;
   extern static function void print_bindings(vmm_object root = null);
   extern static function void check_bindings(vmm_object root = null);
   extern static function void report_unbound(vmm_object root = null);
endclass: vmm_tlm

typedef class vmm_rw_access;
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

class vmm_tlm_extension_base extends vmm_data;
   `vmm_data_new(vmm_tlm_extension_base)

   virtual function vmm_tlm_extension_base clone();
      `vmm_error(log,"Virtual base class function clone is not extended.");
   endfunction: clone
   
   virtual function void copy_from(vmm_tlm_extension_base ext);
      `vmm_error(log,"Virtual base class function copy_from is not extended.");
   endfunction: copy_from
  
   static function int max_num_extensions(bit increment = 0);
      static int max_num = 0;
      if (increment) ++max_num;
      max_num_extensions = max_num;
   endfunction: max_num_extensions

   static function int register_extension;
      register_extension = (max_num_extensions(1) - 1);
   endfunction: register_extension
endclass: vmm_tlm_extension_base

class vmm_tlm_extension #(type DATA = vmm_tlm_extension_base) extends vmm_tlm_extension_base;
   const static int ID = vmm_tlm_extension_base::register_extension();
endclass: vmm_tlm_extension

class vmm_tlm_generic_payload extends vmm_rw_access;
   typedef enum {TLM_READ_COMMAND = 0,
	             TLM_WRITE_COMMAND = 1,
    	         TLM_IGNORE_COMMAND = 2
                 }tlm_command;
   typedef enum {TLM_OK_RESPONSE = 1,
                 TLM_INCOMPLETE_RESPONSE = 0,
                 TLM_GENERIC_ERROR_RESPONSE = -1,
                 TLM_ADDRESS_ERROR_RESPONSE = -2,
                 TLM_COMMAND_ERROR_RESPONSE = -3,
                 TLM_BURST_ERROR_RESPONSE = -4,
                 TLM_BYTE_ENABLE_ERROR_RESPONSE = -5
                 }tlm_response_status; 

   rand longint              m_address;
   rand tlm_command          m_command;
   rand byte                 m_data[];
   rand int unsigned         m_length;
        tlm_response_status  m_response_status;
        bit                  m_dmi_allowed = 0;
   rand byte                 m_byte_enable[];
   rand int unsigned         m_byte_enable_length;
   rand int unsigned         m_streaming_width;
        int unsigned         min_m_length;
        int unsigned         max_m_length;
        int unsigned         min_m_byte_enable_length;
        int unsigned         max_m_byte_enable_length;
        vmm_tlm_extension_base m_extensions[];
    
   function vmm_tlm_extension_base set_extension(int index, vmm_tlm_extension_base ext);
     vmm_tlm_extension_base tmp = m_extensions[index];
     $cast(m_extensions[index], ext);
     set_extension = tmp;
   endfunction: set_extension
   
   function vmm_tlm_extension_base get_extension(int index);
     get_extension = m_extensions[index];
   endfunction: get_extension
   
   function void clear_extension(int index);
     m_extensions[index] = null;
   endfunction: clear_extension

   `vmm_data_new(vmm_tlm_generic_payload)
   function new(string name = "");
      super.new(
`ifdef VMM_12_UNDERPIN_STDLIB
`ifdef VMM_12_UNDERPIN_VMM_DATA
      null,name
`endif
`endif
	  );
      min_m_length = 0;
      max_m_length = 16;
      min_m_byte_enable_length = 0;
      max_m_byte_enable_length = 256;
      m_extensions = new[ vmm_tlm_extension_base::max_num_extensions() ];
   endfunction	

   `vmm_data_member_begin(vmm_tlm_generic_payload)
	  `vmm_data_member_scalar(m_address, DO_ALL)
	  `vmm_data_member_enum(m_command, DO_ALL)
	  `vmm_data_member_scalar_da(m_data, DO_ALL)
	  `vmm_data_member_scalar(m_length, DO_ALL)
	  `vmm_data_member_enum(m_response_status, DO_ALL)
	  `vmm_data_member_scalar(m_dmi_allowed, DO_ALL)
	  `vmm_data_member_scalar_da(m_byte_enable, DO_ALL)
	  `vmm_data_member_scalar(m_byte_enable_length, DO_ALL)
	  `vmm_data_member_scalar(m_streaming_width, DO_ALL)
	  `vmm_data_member_scalar(min_m_length, DO_COPY)
	  `vmm_data_member_scalar(max_m_length, DO_COPY)
	  `vmm_data_member_scalar(max_m_byte_enable_length, DO_COPY)
	  `vmm_data_member_vmm_data_da(m_extensions, DO_ALL, DO_DEEP)
   `vmm_data_member_end(vmm_tlm_generic_payload)

   constraint c_length_valid
     { m_data.size == m_length; 
       m_length>min_m_length;          }
   constraint c_data_size_reasonable
     { m_length<=max_m_length;          }
   constraint c_byte_enable_valid
     { m_byte_enable.size == m_byte_enable_length; 
       m_byte_enable_length>min_m_byte_enable_length; }
   constraint c_byte_enable_size_reasonable
     { m_byte_enable_length<=max_m_byte_enable_length; }
     
endclass: vmm_tlm_generic_payload

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_base extends vmm_object;

   function new(vmm_object parent, string name);
      super.new(parent,name);
   endfunction: new

   virtual function void print_bindings();
   endfunction: print_bindings

   virtual function void check_bindings();
   endfunction: check_bindings
   
   virtual function void report_unbound();
   endfunction: report_unbound
endclass: vmm_tlm_base

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_xactor extends vmm_xactor;

   function new(string name="", string inst="");
      super.new(name,inst);
   endfunction: new

   virtual function vmm_tlm::sync_e nb_transport_fw(int id = -1, vmm_data trans, ref vmm_tlm::phase_e ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_fw is not extended."); 
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(int id = -1, vmm_data trans, ref vmm_tlm::phase_e ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
   endfunction 

   virtual task b_transport(int id = -1, vmm_data trans,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport

   virtual function void write(int id = -1, vmm_data trans);
      `vmm_error(log,"Virtual base class function write is not extended."); 
   endfunction : write
endclass: vmm_tlm_xactor


typedef class vmm_tlm_export_base;
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_port_base #(type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_base;

   `VMM_LOG log;
   /* local */ protected vmm_tlm_export_base#(DATA,PHASE) m_binding; 

   /* local */ protected int peer_id = -1; 

   /* local */ protected vmm_tlm_port_base#(DATA,PHASE) parent_port;
   /* local */ protected vmm_tlm_port_base#(DATA,PHASE) child_port;
   /* local */ bit is_imported = 0; 
   /* local */ bit is_nb = 0; 
   
   function new(vmm_object parent, string name , `VMM_LOG log);
      super.new(parent,name);
      if(log == null) begin
         this.log = new("vmm_tlm_port_base","class");
      end
      else
         this.log = log;
   endfunction: new
  
   function void tlm_bind(vmm_tlm_export_base#(DATA,PHASE) peer, int id = -1, string fname = "", int lineno = 0);
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_bind of port %s in file %s line %d", this.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_bind of port %s", this.get_object_hiername()));
         return;
      end
      if(this.m_binding != null ) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text(`vmm_sformatf("Binding already exists for port %s. Binding request to export %s ignored.", this.get_object_hiername(), peer.get_object_hiername()))); 
            log.end_msg();
         end
         return;
      end
      if(this.is_nb != peer.is_nb) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Trying to connect non-blocking interface with blocking interface in file %s in line %d",fname,lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Trying to connect non-blocking interface with blocking interface"));
         return;
      end
      if(peer.bind_peer(this,id))  begin
         this.m_binding = peer;
         this.peer_id = id;
      end
   endfunction: tlm_bind

   /* local */ function void bind_peer(vmm_tlm_export_base#(DATA,PHASE) peer, int id = -1);
      this.m_binding = peer; 
      this.peer_id = id;
   endfunction : bind_peer

   function void tlm_import(vmm_tlm_port_base#(DATA,PHASE) peer, string fname = "", int lineno = 0); 
      vmm_tlm_port_base#(DATA,PHASE) child, parent;
      vmm_object _obj_peer,  _obj_this ; 
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of port %s, in file %s in line %d", this.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of port %s", this.get_object_hiername()));
         return;
      end
      if(($cast(_obj_peer,peer.get_parent_object())) && ($cast(_obj_this, this.get_parent_object()))) begin
         if(_obj_this == _obj_peer.get_parent_object()) begin
            parent = this;
            child  = peer; 
         end  
         else if(_obj_this.get_parent_object() == _obj_peer) begin
            parent = peer;
            child  = this; 
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship, in file %s in line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship",this.get_object_hiername() , peer.get_object_hiername()));
            return;
         end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text("Parent/Child of ports not defined.Please ensure tlm_import is called only for child_port.tlm_import(parent_port)")); 
            log.end_msg();
         end
         parent = peer;
         child = this;
      end     
      if(child.is_imported == 1) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Port %s is already imported. Imported port cannot be imported by %s in file %s in line %d",child.get_object_hiername(), parent.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Port %s is already imported. Imported port cannot be imported by %s",child.get_object_hiername(), parent.get_object_hiername()));
         return;
      end
      if(child.m_binding != null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Port %s has a binding. Bounded ports cannot be imported in file %s in line %d",child.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Port %s has a binding. Bounded ports cannot be imported",child.get_object_hiername()));
         return;
      end
      child.parent_port = parent;
      parent.child_port = child;
      child.is_imported = 1;
   endfunction : tlm_import

   function void print_bindings();
      if(this.m_binding == null)
      begin
         if(this.parent_port != null)
            `vmm_note(log,`vmm_sformatf("[Port] %s (child) ---> [Port] %s (parent)",this.get_object_hiername(), this.parent_port.get_object_hiername()));
         else      
            `vmm_note(log,`vmm_sformatf("Port %s is not bound to any Export or (Hierarchical) Port",this.get_object_hiername()));
         if(this.child_port != null)
            `vmm_note(log,`vmm_sformatf("[Port] %s (parent) <--- [Port] %s (child)",this.get_object_hiername(), this.child_port.get_object_hiername()));
      end   
      else
      begin
         `vmm_note(log,`vmm_sformatf("[Port] %s (%d) <---> [Export] %s",this.get_object_hiername(), this.peer_id, this.m_binding.get_object_hiername()));
         if(this.child_port != null)
            `vmm_note(log,`vmm_sformatf("[Port] %s (parent) <--- [Port] %s (child)",this.get_object_hiername(), this.child_port.get_object_hiername()));
      end   
   endfunction: print_bindings

   function void check_bindings();
      if(this.m_binding == null)
      begin
         if(this.parent_port == null)
            `vmm_warning(log,`vmm_sformatf("Port %s is not bound to any Export or (Hierarchical) Port",this.get_object_hiername()));
      end   
   endfunction: check_bindings
   
   function void report_unbound();
      if(this.m_binding == null)
      begin
         if(this.parent_port == null)
            `vmm_warning(log,`vmm_sformatf("Port %s is not bound to any Export or (Hierarchical) Port",this.get_object_hiername()));
      end   
   endfunction: report_unbound

   function vmm_tlm_export_base#(DATA,PHASE) get_peer();
      return this.m_binding;
   endfunction: get_peer

   function void tlm_unbind(string fname="", int lineno = 0);
      if(this.m_binding == null) begin
         `vmm_warning(log,`vmm_sformatf("No binding exists for port %s. Cannot unbind",this.get_object_hiername()));
         return;
      end
      if(this.m_binding.unbind_peer(this)) begin
         this.m_binding = null;
         this.peer_id = -1;
      end
   endfunction: tlm_unbind

   function int get_peer_id();
      return this.peer_id;
   endfunction : get_peer_id

   /* local */ function void unbind_peer();
      this.m_binding = null;
      this.peer_id = -1;
   endfunction : unbind_peer 

   virtual function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_fw is not extended."); 
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
   endfunction 

   virtual task b_transport(DATA trans,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport
   
endclass: vmm_tlm_port_base
   
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_export_base #(type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_base;

   `VMM_LOG log;
   /* local */ vmm_tlm_port_base#(DATA,PHASE) bindings[$];
   /* local */ protected int m_bindings; 
   /* local */ protected vmm_tlm_port_base#(DATA,PHASE) bindings_id[int]; 
   /* local */ local int available_id = 0;
  
   /* local */ protected vmm_tlm_export_base#(DATA,PHASE) parent_export;
   /* local */ protected vmm_tlm_export_base#(DATA,PHASE) child_export;
   /* local */ protected bit is_imported = 0; 
   /* local */ bit is_nb = 0; 
   
   local int m_max_binds = 1;
   local int m_min_binds = 0;
   function new(vmm_object parent, string name, int max_binds = 1, int min_binds = 0 , `VMM_LOG log);
      super.new(parent,name);
      this.m_max_binds = max_binds;
      this.m_min_binds = min_binds;
      if(log == null) begin
         this.log = new("vmm_tlm_export_base","class");   
      end
      else
         this.log = log;
   endfunction: new

   function void tlm_bind(vmm_tlm_port_base#(DATA,PHASE) peer , int id = -1, string fname = "", int lineno = 0);
      int alloted_id = -1;
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_bind of export %s in file %s line %d", this.get_object_hiername(),fname,lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_bind of export %s", this.get_object_hiername()));
         return;
      end
      if(this.m_bindings >= this.m_max_binds) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Transport Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export in file %s line %d", this.get_object_hiername(), this.m_max_binds, fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Transport Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export", this.get_object_hiername(), this.m_max_binds));
         return;
      end
      if(peer.get_peer() != null) begin 
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text(`vmm_sformatf("Port %s already has a binding.Cannot bind a bounded port to %s",peer.get_object_hiername(), this.get_object_hiername()))); 
            log.end_msg();
         end
         return;
      end
      if((id >= 0 ) && ( this.bindings_id.exists(id))) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Peer id %d already exists for transport export %d. Specified positive ID must be unique, in file %s line %d", id, this.get_object_hiername(),fname,lineno));
         else
            `vmm_error(log,`vmm_sformatf("Peer id %d already exists for transport export %d. Specified positive ID must be unique", id, this.get_object_hiername()));
         return;
      end
      if(this.is_nb != peer.is_nb) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Trying to connect non-blocking interface with blocking interface in file %s line %d",fname,lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Trying to connect non-blocking interface with blocking interface"));
         return;
      end
      if(id < 0 ) begin
         for(int i = 0 ; i <= bindings_id.num() ; i++) begin 
            if(!bindings_id.exists(i)) begin
               available_id = i; 
               break;
            end
         end
         alloted_id = available_id;
      end
      else begin
         alloted_id = id;
      end
      this.bindings_id[alloted_id] = peer;
      this.bindings.push_back(peer);
      peer.bind_peer(this,alloted_id);
      m_bindings++;
   endfunction: tlm_bind

   function void print_bindings();
      if(this.m_bindings == 0)
      begin
         if(this.parent_export != null)
            `vmm_note(log,`vmm_sformatf("[Export] %s (child) ---> [Export] %s (parent)",this.get_object_hiername(), this.parent_export.get_object_hiername()));
         else      
            `vmm_note(log,`vmm_sformatf("[Export] %s is not bound to any [Port] or (Hierarchical) Export",this.get_object_hiername()));
         if(this.child_export != null)
            `vmm_note(log,`vmm_sformatf("[Export] %s (parent) <--- [Export] %s (child)",this.get_object_hiername(), this.child_export.get_object_hiername()));
      end   
      else
      begin
         for(int i = 0; i < m_bindings ; i++)
         begin
            `vmm_note(log,`vmm_sformatf("[Export] %s <---> [Port] %s (%d)",this.get_object_hiername(), this.bindings[i].get_object_hiername(), this.get_peer_id(bindings[i])));
         end
         if(this.child_export != null)
            `vmm_note(log,`vmm_sformatf("[Export] %s (parent) <--- [Export] %s (child)",this.get_object_hiername(), this.child_export.get_object_hiername()));
      end
   endfunction: print_bindings

   function void check_bindings();
      if(this.m_bindings < this.m_min_binds)
      begin
         `vmm_warning(log,`vmm_sformatf("[Export] %s is not bound",this.get_object_hiername()));
      end
   endfunction: check_bindings
   
   function void report_unbound();
      if(this.m_bindings < this.m_min_binds)
      begin
         `vmm_warning(log,`vmm_sformatf("[Export] %s is not bound",this.get_object_hiername()));
      end
      if(this.m_bindings == 0)
      begin
         if(this.parent_export == null)
            `vmm_warning(log,`vmm_sformatf("[Export] %s is not bound to any [Port] or (Hierarchical) Export",this.get_object_hiername()));
      end
   endfunction: report_unbound
   
   /* local */ function int bind_peer(vmm_tlm_port_base#(DATA,PHASE) peer, inout int id );
      if(this.m_bindings >= this.m_max_binds) begin 
         `vmm_error(log,`vmm_sformatf("Transport Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export", this.get_object_hiername(), this.m_max_binds));
         return 0;
      end
      if((id >= 0 ) && ( this.bindings_id.exists(id))) begin
         `vmm_error(log,`vmm_sformatf("Peer id %d already exists for transport export %s. Specified positibve ID must be unique", id, this.get_object_hiername()));
         return 0;
      end
      if(id < 0 ) begin
         for(int i = 0 ; i <= bindings_id.num() ; i++) begin 
            if(!bindings_id.exists(i)) begin
               available_id = i; 
               break;
            end
         end
         id = available_id;
      end
      this.bindings_id[id] = peer;
      this.bindings.push_back(peer);
      this.m_bindings++;
      return 1;
   endfunction : bind_peer

   function void tlm_import(vmm_tlm_export_base#(DATA,PHASE) peer, string fname = "", int lineno = 0);
      vmm_tlm_export_base#(DATA,PHASE) child, parent;
      vmm_object _obj_peer, _obj_this; 
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of export %s in file %s line %d", this.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of export %s", this.get_object_hiername()));
         return;
      end
      if(($cast(_obj_peer,peer.get_parent_object())) && ($cast(_obj_this, this.get_parent_object()))) begin
         if(_obj_this == _obj_peer.get_parent_object()) begin
            parent = this;
            child  = peer; 
         end  
         else if(_obj_this.get_parent_object() == _obj_peer) begin
            parent = peer;
            child  = this; 
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent-child ports. Port %s and %s do not have a parent child relationship, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent-child ports. Port %s and %s do not have a parent child relationship",this.get_object_hiername() , peer.get_object_hiername()));
            return;
         end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text("Parent-child relationship could not be established.Please ensure tlm_import is called only for child_port.tlm_import(parent_port)")); 
            log.end_msg();
         end
         parent = peer;
         child = this;
      end     
      if(child.is_imported == 1) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Export %s is already imported. Imported export cannot be imported by %s in file %s line %d",child.get_object_hiername(), parent.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Export %s is already imported. Imported export cannot be imported by %s",child.get_object_hiername(), parent.get_object_hiername()));
         return;
      end
      if(child.m_bindings >0) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Export %s has  bindings. Bounded exports cannot be imported in file %s line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Export %s has  bindings. Bounded exports cannot be imported",child.get_object_hiername()));
         return;
      end
      child.parent_export = parent;
      parent.child_export = child;
      child.is_imported = 1;
   endfunction : tlm_import

   function int get_n_peers();
      return this.m_bindings;
   endfunction : get_n_peers

   function void get_peers(output vmm_tlm_port_base#(DATA,PHASE) peers[$]);
      peers = this.bindings;
   endfunction : get_peers

   function int get_peer_id(vmm_tlm_port_base#(DATA,PHASE) peer);
      if(peer == null) begin
         `vmm_error(log,`vmm_sformatf("Null port reference passed to get_peer_id of export %s", this.get_object_hiername()));
      end
      return peer.get_peer_id();
   endfunction : get_peer_id

   function vmm_tlm_port_base#(DATA,PHASE) get_peer(int id = -1);
      if(this.bindings.size() == 1)
         return this.bindings[0];
      else if(id < 0 ) begin 
         `vmm_warning(log,`vmm_sformatf("Invalid id %d specfied for transport export %s get_peer method.Positive id is required",id, this.get_object_hiername()));
      end
      else 
         return this.bindings_id[id];
   endfunction : get_peer

   function void tlm_unbind(vmm_tlm_port_base#(DATA,PHASE) peer = null, int id= -1, string fname="", int lineno = 0);
      vmm_tlm_port_base#(DATA,PHASE) binding, temp_binding ;
      int location[$];
      if((peer == null ) && (id < 0 ) ) begin
         foreach(this.bindings[i]) begin
            binding = this.bindings[i];
            binding.unbind_peer();
         end
         this.bindings.delete();
         this.bindings_id.delete();
         this.m_bindings = 0;
         return ;
      end

      if(peer != null ) begin
         location = this.bindings.find_first_index(binding) with ( binding == peer);
         if(location.size() == 0 ) begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("No binding exists between transport export %s and transport port %s. Cannot unbind, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log,`vmm_sformatf("No binding exists between transport export %s and transport port %s. Cannot unbind",this.get_object_hiername() , peer.get_object_hiername()));
            return ;
         end 
         else begin
            this.bindings.delete(location[0]);
            peer.unbind_peer();
            this.m_bindings--; 
            location = this.bindings_id.find_first_index(binding) with ( binding == peer); 
            this.bindings_id.delete(location[0]);
            return;
         end
      end

      if(peer == null && id >= 0) begin
         if(this.bindings_id.exists(id)) begin
             binding = this.bindings_id[id];
             this.bindings_id.delete(id);
             binding.unbind_peer();
             location = this.bindings.find_first_index(temp_binding) with ( binding == temp_binding);
             this.bindings.delete(location[0]);
             this.m_bindings--;
             return;
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log, `vmm_sformatf("No binding with id %d exists for transport  export %s. Cannot unbind, in file %s line %d", id, this.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log, `vmm_sformatf("No binding with id %d exists for transport  export %s. Cannot unbind  ", id, this.get_object_hiername()));
            return ;
         end
       end
   endfunction : tlm_unbind 

   /* local */ function int unbind_peer(vmm_tlm_port_base#(DATA,PHASE) peer);
      int location[$];
      vmm_tlm_port_base#(DATA,PHASE) binding;
      location = this.bindings.find_first_index(item) with ( binding == peer);
      this.bindings.delete(location[0]);
      this.m_bindings--;
      location = this.bindings_id.find_first_index(binding) with ( binding == peer);
      this.bindings_id.delete(location[0]);
      return 1;
   endfunction : unbind_peer

   virtual function vmm_tlm::sync_e nb_transport_fw(int id =-1, DATA trans,  ref PHASE ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_fw is not extended."); 
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans,  ref PHASE ph, ref int delay, input int id = -1);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
   endfunction 

   virtual task b_transport(int id = -1, DATA trans ,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport
   
endclass: vmm_tlm_export_base
   
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_b_transport_port #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data) extends vmm_tlm_port_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_b_transport_port","class");

   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null);
   endfunction: new

   virtual task b_transport(DATA trans , ref int delay);
      if(this.parent_port == null  ) 
          this.m_binding.b_transport(this.peer_id, trans, delay);
      else
          this.parent_port.b_transport( trans , delay );
   endtask : b_transport

endclass : vmm_tlm_b_transport_port

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_b_transport_export #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data) extends vmm_tlm_export_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_b_transport_export","class");
   /* local */ local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds, ((parent != null ) && $cast(_obj,parent))? _obj.get_log() : null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_b_transport_export constructor");
      this.m_parent = parent;
   endfunction: new

   virtual task b_transport(int id = -1, DATA trans, ref int delay);
      if(this.child_export == null) 
         this.m_parent.b_transport(id, trans, delay);
      else
         this.child_export.b_transport(id,trans,delay);
   endtask : b_transport

endclass : vmm_tlm_b_transport_export

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_fw_port #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_fw_port","class");
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ?_obj.get_log() : null);
      this.is_nb = 1;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      if(this.parent_port == null)
         nb_transport_fw = this.m_binding.nb_transport_fw(this.peer_id, trans,  ph, delay);
      else
         nb_transport_fw = this.parent_port.nb_transport_fw(trans,  ph, delay);
         
   endfunction : nb_transport_fw

endclass : vmm_tlm_nb_transport_fw_port

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_fw_export #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_fw_export","class");
   local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds ,((parent != null) && $cast(_obj, parent)) ? _obj.get_log() : null);
      this.m_parent = parent;
      this.is_nb = 1;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_fw(int id = 1, DATA trans,  ref PHASE ph, ref int delay);
      if(this.child_export == null)
         nb_transport_fw = this.m_parent.nb_transport_fw(id, trans, ph, delay);
      else
         nb_transport_fw = this.child_export.nb_transport_fw(id, trans, ph, delay);
   endfunction : nb_transport_fw

endclass : vmm_tlm_nb_transport_fw_export

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_port #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_port","class");
   local INITIATOR m_parent;
   
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ?_obj.get_log() : null);
      this.is_nb = 1;
      this.m_parent = parent;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      if(this.parent_port == null)
         nb_transport_fw = this.m_binding.nb_transport_fw(this.peer_id, trans,  ph, delay);
      else
         nb_transport_fw = this.parent_port.nb_transport_fw(trans,  ph, delay);
   endfunction : nb_transport_fw

   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      if(this.child_port == null )
         nb_transport_bw = this.m_parent.nb_transport_bw(id, trans, ph, delay);
      else
         nb_transport_bw = this.child_port.nb_transport_bw(trans, ph, delay, id);
   endfunction : nb_transport_bw
   
endclass : vmm_tlm_nb_transport_port

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_export #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_export","class");
   local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds ,((parent != null) && $cast(_obj, parent)) ? _obj.get_log() : null);
      this.m_parent = parent;
      this.is_nb = 1;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_fw(int id = 1, DATA trans,  ref PHASE ph, ref int delay);
      if(this.child_export == null)
         nb_transport_fw = this.m_parent.nb_transport_fw(id, trans, ph, delay);
      else
         nb_transport_fw = this.child_export.nb_transport_fw(id, trans, ph, delay);
   endfunction : nb_transport_fw

   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      int q[$];
      if(this.parent_export == null )
      begin
         if(id < 0)
         begin
            q = this.bindings_id.find_first_index(x) with (x!=null);
            nb_transport_bw = this.bindings_id[q[0]].nb_transport_bw(trans, ph, delay, id);
         end   
         else
            nb_transport_bw = this.bindings_id[id].nb_transport_bw(trans, ph, delay, id);
      end
      else
         nb_transport_bw = this.parent_export.nb_transport_bw(trans, ph, delay, id);
   endfunction : nb_transport_bw

endclass : vmm_tlm_nb_transport_export

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_bw_port #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA,PHASE);
                                            
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_bw_port","class");
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name, ((parent != null ) && $cast(_obj,parent))? _obj.get_log() : null );
      this.is_nb = 1;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      if(this.parent_port == null )
         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph, delay, this.peer_id);
      else
         nb_transport_bw = this.parent_port.nb_transport_bw(trans, ph, delay);
   endfunction : nb_transport_bw

endclass : vmm_tlm_nb_transport_bw_port

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_nb_transport_bw_export #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_export_base#(DATA,PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_bw_export","class");
   local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds,((parent != null) && $cast(_obj,parent))? _obj.get_log(): null  );
      this.m_parent = parent;
      this.is_nb = 1;
   endfunction: new

   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      if(this.child_export == null )
         nb_transport_bw = this.m_parent.nb_transport_bw(id, trans, ph, delay);
      else
         nb_transport_bw = this.child_export.nb_transport_bw(trans, ph, delay, id);
   endfunction : nb_transport_bw

endclass : vmm_tlm_nb_transport_bw_export

typedef class vmm_tlm_analysis_export_base;

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_analysis_port_base #(type DATA = vmm_data) extends vmm_tlm_base;

   `VMM_LOG log;

   /* local */ protected vmm_tlm_analysis_export_base#(DATA) bindings[$];

   /* local */ protected int unsigned m_bindings; 

   /* local */ protected vmm_tlm_analysis_port_base#(DATA) parent_port, child_port;
   /* local */ protected bit is_imported = 0;
  
   function new(vmm_object parent, string name , `VMM_LOG log);
      super.new(parent,name);
      if(log == null)
         this.log = new("vmm_tlm_analysis_port_base","class");
      else
         this.log = log;
   endfunction : new 

   function get_peers(output vmm_tlm_analysis_export_base#(DATA) peers[$]);
      peers = this.bindings;
   endfunction : get_peers

   function int get_n_peers();
      return this.m_bindings; 
   endfunction : get_n_peers

   function int get_peer_id(vmm_tlm_analysis_export_base#(DATA) peer); 
      if(peer == null) begin
         `vmm_error(log,`vmm_sformatf("Null port reference passed to get_peer_id of port %s", this.get_object_hiername()));
         return -1;
      end
      return peer.get_peer_id(this);
   endfunction : get_peer_id

   function vmm_tlm_analysis_export_base#(DATA) get_peer(int id = -1);
      if(this.bindings.size() == 1)
         return this.bindings[0];
      else
         return this.bindings[id]; 
   endfunction : get_peer

   function void tlm_bind(vmm_tlm_analysis_export_base#(DATA) peer, int id = -1, string fname = "", int lineno = 0); 
      int location[$];
      vmm_tlm_analysis_export_base#(DATA) binding;
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_bind of analysis port %s in file %s line %d", this.get_object_hiername(),fname,lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_bind of analysis port %s", this.get_object_hiername()));
         return;
      end
      location = this.bindings.find_first_index(binding) with (binding == peer);
      if(location.size() > 0 ) begin
         `vmm_warning(log,`vmm_sformatf("Binding already exists between analysis port %s and analysis export %s. Binding request is ignored", this.get_object_hiername(), peer.get_object_hiername()));
         return;
      end
      if(peer.bind_peer(this,id)) begin 
         this.bindings.push_back(peer);
         this.m_bindings++;
      end
   endfunction : tlm_bind

   /* local */ function int  bind_peer(vmm_tlm_analysis_export_base#(DATA) peer);
      this.bindings.push_back(peer);
      this.m_bindings++;
   endfunction : bind_peer

   function void tlm_unbind(vmm_tlm_analysis_export_base#(DATA) peer = null, string fname="", int lineno = 0);
       vmm_tlm_analysis_export_base#(DATA) binding;
       int location[$];
       if(peer == null ) begin
          foreach(this.bindings[i]) begin
             binding = this.bindings[i];
             binding.unbind_peer(this);
          end
          this.bindings.delete();
          this.m_bindings = 0;
       end
       else begin
          location = this.bindings.find_first_index(binding) with ( binding == peer);
          if(location.size() == 0 ) begin 
             if(fname != "" && lineno != 0)
                `vmm_error(log,`vmm_sformatf("No binding exists between analysis port %s and analysis export %s. Cannot unbind, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno)); 
             else   
                `vmm_error(log,`vmm_sformatf("No binding exists between analysis port %s and analysis export %s. Cannot unbind",this.get_object_hiername() , peer.get_object_hiername())); 
             return;
          end
          binding = this.bindings[location[0]];
          this.bindings.delete(location[0]);
          this.m_bindings--;
          binding.unbind_peer(this);
       end
   endfunction : tlm_unbind
  
   /* local */  function void unbind_peer(vmm_tlm_analysis_export_base#(DATA) peer);
       int location[$];
       vmm_tlm_analysis_export_base#(DATA) binding;
       location = this.bindings.find_first_index(binding) with ( peer == binding);
       this.bindings.delete(location[0]);
       this.m_bindings--;
   endfunction : unbind_peer

   function void tlm_import(vmm_tlm_analysis_port_base#(DATA) peer, string fname = "", int lineno = 0); 
      vmm_tlm_analysis_port_base#(DATA) child, parent;
      vmm_object _obj_peer, _obj_this; 
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of analysis port %s in file %s line %d", this.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_import of analysis port %s", this.get_object_hiername()));
         return;
      end
      if(($cast(_obj_peer,peer.get_parent_object())) && ($cast(_obj_this, this.get_parent_object()))) begin
         if(_obj_this == _obj_peer.get_parent_object()) begin
            parent = this;
            child  = peer; 
         end  
         else if(_obj_this.get_parent_object() == _obj_peer) begin
            parent = peer;
            child  = this; 
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship",this.get_object_hiername() , peer.get_object_hiername()));
            return;
         end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text("Parent not defined.Please ensure tlm_import is called only for child_port.tlm_import(parent_port)")); 
            log.end_msg();
         end
         parent = peer;
         child = this;
      end     
      if(child.is_imported == 1) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Analysis Port %s is already imported. Imported port cannot be imported again, in file %s line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Analysis Port %s is already imported. Imported port cannot be imported again",child.get_object_hiername()));
         return;
      end
      if(child.m_bindings > 0) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Analysis Port %s has a binding. Bounded ports cannot be imported, in file %s in line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Analysis Port %s has a binding. Bounded ports cannot be imported",child.get_object_hiername()));
         return;
      end
      child.parent_port = parent;
      parent.child_port = child;
      child.is_imported = 1;
   endfunction : tlm_import

   function void print_bindings();
      if(this.m_bindings == 0)
      begin
         if(this.parent_port != null)
            `vmm_note(log,`vmm_sformatf("[Analysis port] %s (child) ---> [Analysis port] %s (parent)",this.get_object_hiername(), this.parent_port.get_object_hiername()));
         else      
            `vmm_note(log,`vmm_sformatf("Analysis port %s is not bound to any Analysis export or (Hierarchical) Analysis port",this.get_object_hiername()));
         if(this.child_port != null)
            `vmm_note(log,`vmm_sformatf("[Analysis port] %s (parent) <--- [Analysis port] %s (child)",this.get_object_hiername(), this.child_port.get_object_hiername()));
      end   
      else
      begin
         for(int i = 0; i < m_bindings ; i++)
         begin
            `vmm_note(log,`vmm_sformatf("[Analysis port] %s (%d) <---> [Analysis export] %s",this.get_object_hiername(), this.get_peer_id(bindings[i]), this.bindings[i].get_object_hiername()));
         end
         if(this.child_port != null)
            `vmm_note(log,`vmm_sformatf("[Analysis port] %s (parent) <--- [Analysis port] %s (child)",this.get_object_hiername(), this.child_port.get_object_hiername()));
      end
   endfunction: print_bindings

   function void check_bindings();
      if(this.m_bindings == 0)
      begin
         if(this.parent_port == null)
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text(`vmm_sformatf("Analysis port %s is not bound to any Analysis export or (Hierarchical) Analysis port",this.get_object_hiername()))); 
               log.end_msg();
            end
      end
   endfunction: check_bindings
   
   function void report_unbound();
      if(this.m_bindings == 0)
      begin
         if(this.parent_port == null)
            if (log.start_msg(vmm_log::INTERNAL_TYP, vmm_log::DEBUG_SEV)) begin
               void'(log.text(`vmm_sformatf("Analysis port %s is not bound to any Analysis export or (Hierarchical) Analysis port",this.get_object_hiername()))); 
               log.end_msg();
            end
      end
   endfunction: report_unbound
   
   virtual function void write(DATA trans);
      `vmm_error(log,"Virtual base class function write  is not extended."); 
   endfunction: write

endclass : vmm_tlm_analysis_port_base

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_analysis_export_base #(type DATA = vmm_data ) extends vmm_tlm_base;

   `VMM_LOG log;

   /* local */ protected vmm_tlm_analysis_port_base#(DATA) bindings[$]; 
   
   /* local */ protected vmm_tlm_analysis_port_base#(DATA) bindings_id[int];
   /* local */ local int available_id = 0;
   /* local */ protected int unsigned m_bindings;

   local int unsigned m_max_binds = 1;
   local int unsigned m_min_binds = 0; 

   protected vmm_tlm_analysis_export_base#(DATA) parent_export, child_export;
   protected bit is_imported = 0;

   function  new(vmm_object parent, string name , int max_binds = 1 , int min_binds = 0, `VMM_LOG log);
      super.new(parent, name); 
      this.m_max_binds = max_binds;
      this.m_min_binds = min_binds;
      if(log == null) 
         this.log = new("vmm_tlm_analysis_export_base","class");
      else
         this.log = log;
   endfunction : new

   function void tlm_bind(vmm_tlm_analysis_port_base#(DATA) peer, int id = -1, string fname = "", int lineno = 0);
      vmm_tlm_analysis_port_base#(DATA) binding;
      int location[$];
      int alloted_id = -1;
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_bind of analysis export %s in file %s in line %d", this.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null port reference passed to tlm_bind of analysis export %s", this.get_object_hiername()));
         return;
      end
      if(this.m_bindings >= this.m_max_binds) begin 
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Analysis Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export, in file %s in line %d", this.get_object_hiername(), this.m_max_binds, fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Analysis Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export", this.get_object_hiername(), this.m_max_binds));
         return;
      end
      location = this.bindings.find_first_index(binding) with (binding == peer);
      if(location.size() > 0 ) begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text(`vmm_sformatf("Binding already exists between analysis export %s and analysis port %s. Binding request is ignored", this.get_object_hiername(), peer.get_object_hiername()))); 
            log.end_msg();
         end
         return;
      end 
      if((id >= 0 ) && ( this.bindings_id.exists(id))) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Peer id %d already exists for analysis export %s. Specified positibve ID must be unique, in file %s line %d", id, this.get_object_hiername(),fname,lineno));
         else
            `vmm_error(log,`vmm_sformatf("Peer id %d already exists for analysis export %s. Specified positibve ID must be unique", id, this.get_object_hiername()));
         return;
      end
      if(id < 0 ) begin
         for(int i = 0 ; i <= bindings_id.num() ; i++) begin 
            if(!bindings_id.exists(i)) begin
               available_id = i; 
               break;
            end
         end
         alloted_id = available_id;
      end
      else begin
         alloted_id = id;
      end
      this.bindings_id[alloted_id] = peer;
      this.bindings.push_back(peer);
      peer.bind_peer(this); 
      m_bindings++;
   endfunction : tlm_bind

   /* local */ function int bind_peer(vmm_tlm_analysis_port_base#(DATA) peer, int id = -1);
      if(this.m_bindings >= this.m_max_binds) begin 
         `vmm_error(log,`vmm_sformatf("Analysis Export %s already has maximum %d allowed bindings. More bindings are not allowed for this export", this.get_object_hiername(), this.m_max_binds));
         return 0;
      end
      if((id >= 0 ) && ( this.bindings_id.exists(id))) begin
         `vmm_error(log,`vmm_sformatf("Peer id %d already exists for analysis export %d. Specified positibve ID must be unique", id, this.get_object_hiername()));
         return 0;
      end
      if(id < 0 ) begin
         for(int i = 0 ; i <= bindings_id.num() ; i++) begin 
            if(!bindings_id.exists(i)) begin
               available_id = i; 
               this.bindings_id[available_id] = peer;
               break;
            end
         end
      end
      else
         this.bindings_id[id] = peer;
      this.bindings.push_back(peer);
      this.m_bindings++;
      return 1;
   endfunction : bind_peer
      
   function void tlm_unbind(vmm_tlm_analysis_port_base#(DATA) peer, int id= -1, string fname="", int lineno = 0);
      vmm_tlm_analysis_port_base#(DATA) binding , temp_binding;
      int location[$];
      if((peer == null ) && (id < 0 ) ) begin
         foreach(this.bindings[i]) begin
            binding = this.bindings[i];
            binding.unbind_peer(this);
         end
         this.bindings.delete();
         this.bindings_id.delete();
         this.m_bindings = 0;
         return ;
      end

      if(peer != null ) begin
         location = this.bindings.find_first_index(binding) with ( binding == peer);
         if(location.size() == 0 ) begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("No binding exists between analysis export %s and analysis port %s. Cannot unbind, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else   
               `vmm_error(log,`vmm_sformatf("No binding exists between analysis export %s and analysis port %s. Cannot unbind",this.get_object_hiername() , peer.get_object_hiername()));
            return ;
         end 
         else begin
            this.bindings.delete(location[0]);
            peer.unbind_peer(this);
            this.m_bindings--; 
            location = this.bindings_id.find_first_index(binding) with ( binding == peer); 
            this.bindings_id.delete(location[0]);
            return;
         end
      end

      if(peer == null && id >= 0) begin
         if(this.bindings_id.exists(id)) begin
             binding = this.bindings_id[id];
             this.bindings_id.delete(id);
             binding.unbind_peer(this);
             location = this.bindings.find_first_index(temp_binding) with ( binding == temp_binding);
             this.bindings.delete(location[0]);
             this.m_bindings--;
             return;
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log, `vmm_sformatf("No binding with id %d exists for analysis export %s. Cannot unbind, in file %s in line %d", id, this.get_object_hiername(), fname, lineno));
            else
               `vmm_error(log, `vmm_sformatf("No binding with id %d exists for analysis export %s. Cannot unbind  ", id, this.get_object_hiername()));
            return ;
         end
       end
   endfunction : tlm_unbind 

   /* local */ function void unbind_peer(vmm_tlm_analysis_port_base#(DATA) peer);
      int location[$];
      vmm_tlm_analysis_port_base#(DATA) binding;
      location = this.bindings.find_first_index(item) with ( binding == peer);
      this.bindings.delete(location[0]);
      this.m_bindings--;
      location = this.bindings_id.find_first_index(binding) with ( binding == peer);
      this.bindings_id.delete(location[0]);
   endfunction : unbind_peer

   function void tlm_import(vmm_tlm_analysis_export_base#(DATA) peer, string fname = "", int lineno = 0);
      vmm_tlm_analysis_export_base#(DATA) child, parent;
      vmm_object _obj_peer, _obj_this; 
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_import of analysis export %s in file %s in line %d", this.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Null export reference passed to tlm_import of analysis export %s", this.get_object_hiername()));
         return;
      end
      if(($cast(_obj_peer,peer.get_parent_object())) && ($cast(_obj_this, this.get_parent_object()))) begin
         if(_obj_this == _obj_peer.get_parent_object()) begin
            parent = this;
            child  = peer; 
         end  
         else if(_obj_this.get_parent_object() == _obj_peer) begin
            parent = peer;
            child  = this; 
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship, in file %s in line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else   
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship",this.get_object_hiername() , peer.get_object_hiername()));
            return;
         end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text("Parent not defined.Please ensure tlm_import is called only for child_port.tlm_import(parent_port)")); 
            log.end_msg();
         end
         parent = peer;
         child = this;
      end     
      if(child.is_imported == 1) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Analysis export %s is already imported. Imported export cannot be imported again, in file %s line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Analysis export %s is already imported. Imported export cannot be imported again",child.get_object_hiername()));
         return;
      end
      if(child.m_bindings > 0) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Analysis export %s has a binding. Bounded exports cannot be imported, in file %s in line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Analysis export %s has a binding. Bounded exports cannot be imported",child.get_object_hiername()));
         return;
      end
      child.parent_export = parent;
      parent.child_export = child;
      child.is_imported = 1;
   endfunction : tlm_import

   virtual function void write(int id = -1, DATA trans);
      `vmm_error(log,"Virtual base class function write is not extended."); 
   endfunction: write

   function get_peers(output vmm_tlm_analysis_port_base#(DATA) peers[$]);
      peers = this.bindings;
   endfunction : get_peers
   
   function vmm_tlm_analysis_port_base#(DATA) get_peer(int id = -1 );
      if(this.bindings.size() == 1)
         return this.bindings[0];
      else if(id < 0 ) begin 
         `vmm_warning(log,`vmm_sformatf("Invalid id %d specfied for analysis export %s get_peer method.Positive id is required",id, this.get_object_hiername()));
      end
      else 
         return this.bindings_id[id];
   endfunction : get_peer

   function int unsigned get_n_peers();
      return this.m_bindings;
   endfunction : get_n_peers

   function int get_peer_id(vmm_tlm_analysis_port_base#(DATA) peer); 
      vmm_tlm_analysis_port_base#(DATA) binding;
      int location[$];
      if(peer == null) begin
         `vmm_error(log,`vmm_sformatf("Null port reference passed to get_peer_id of analysis export %s", this.get_object_hiername()));
         return -1;
      end
      location = this.bindings_id.find_first_index(binding) with ( binding == peer);
      if(location.size() == 0 ) begin
         `vmm_warning(log,`vmm_sformatf("No binding exists between analysis export %s and analysis port %s", this.get_object_hiername(), peer.get_object_hiername()));
         return -1;
      end
      else 
         return location[0];
   endfunction : get_peer_id

   function int unsigned get_max_bindings();
      return this.m_max_binds;
   endfunction : get_max_bindings

   function int unsigned get_min_bindings();
      return this.m_min_binds;
   endfunction : get_min_bindings

   function set_max_bindings(int unsigned max);
      this.m_max_binds = max;
   endfunction : set_max_bindings

   function set_min_bindings(int unsigned min);
      this.m_min_binds = min;
   endfunction : set_min_bindings

   function void print_bindings();
      if(this.m_bindings == 0)
      begin
         if(this.parent_export != null)
            `vmm_note(log,`vmm_sformatf("[Analysis export] %s (child) ---> [Analysis export] %s (parent)",this.get_object_hiername(), this.parent_export.get_object_hiername()));
         else      
            `vmm_note(log,`vmm_sformatf("Analysis export %s is not bound to any Analysis port or (Hierarchical) Analysis export",this.get_object_hiername()));
         if(this.child_export != null)
            `vmm_note(log,`vmm_sformatf("[Analysis export] %s (parent) <--- [Analysis export] %s (child)",this.get_object_hiername(), this.child_export.get_object_hiername()));
      end   
      else
      begin
         for(int i = 0; i < m_bindings ; i++)
         begin
            `vmm_note(log,`vmm_sformatf("[Analysis export] %s <---> [Analysis port] %s (%d)",this.get_object_hiername(), this.bindings[i].get_object_hiername(), this.get_peer_id(bindings[i])));
         end
         if(this.child_export != null)
            `vmm_note(log,`vmm_sformatf("[Analysis export] %s (parent) <--- [Analysis export] %s (child)",this.get_object_hiername(), this.child_export.get_object_hiername()));
      end
   endfunction: print_bindings

   function void check_bindings();
      if(this.m_bindings < this.m_min_binds)
      begin
         `vmm_note(log,`vmm_sformatf("Analysis export %s is not bound",this.get_object_hiername()));
      end
   endfunction: check_bindings
   
   function void report_unbound();
      if(this.m_bindings < this.m_min_binds)
      begin
         `vmm_note(log,`vmm_sformatf("Analysis export %s is not bound",this.get_object_hiername()));
      end
      if(this.m_bindings == 0)
      begin
         if(this.parent_export == null)
            `vmm_note(log,`vmm_sformatf("Analysis export %s is not bound to any Analysis port or (Hierarchical) Analysis export",this.get_object_hiername()));
      end      
   endfunction: report_unbound
   
endclass : vmm_tlm_analysis_export_base

typedef class vmm_tlm_analysis_export;
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_analysis_port #(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data) extends vmm_tlm_analysis_port_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_analysis_port","class");
   function new(INITIATOR parent, string name);
       super.new(($cast(_obj,parent)) ? _obj : null, name, ((parent != null ) && $cast(_obj,parent)) ? _obj.get_log(): null);
   endfunction : new

   virtual function void write(DATA trans);
      int id = -1;
      if(this.parent_port == null ) begin
         foreach (this.bindings[i]) begin
            id = this.bindings[i].get_peer_id(this); 
            bindings[i].write(id, trans );
         end
      end
      else
         this.parent_port.write(trans);
   endfunction : write
endclass : vmm_tlm_analysis_port

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_analysis_export #(type TARGET = vmm_tlm_xactor, type DATA = vmm_data) extends vmm_tlm_analysis_export_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_analysis_export","class");
   local TARGET m_parent;

   function  new(TARGET parent, string name , int max_binds = 1 , int min_binds = 0);
      super.new( ($cast(_obj, parent)) ? _obj : null, name, max_binds, min_binds,((parent != null) && $cast(_obj,parent))? _obj.get_log():null);
      this.m_parent = parent;
   endfunction : new 

   virtual function void write(int id = -1, DATA trans);
      if(this.child_export == null)
         this.m_parent.write(id, trans);
      else
         this.child_export.write(id, trans);
   endfunction : write
endclass : vmm_tlm_analysis_export

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
virtual class vmm_tlm_socket_base #(type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_base;

   `VMM_LOG log; 
   /* local */ protected vmm_tlm_socket_base#(DATA,PHASE) m_binding; 
   /* local */ protected int peer_id = -1;

   /* local */ protected vmm_tlm_socket_base#(DATA,PHASE) parent_socket, child_socket;
   /* local */ protected bit is_imported = 0;
   
   function new(vmm_object parent, string name, `VMM_LOG log);
      super.new(parent,name);
      if(log == null)
         this.log = new("vmm_tlm_socket_base","class");
      else
         this.log = log;
   endfunction: new
  
   function void tlm_bind(vmm_tlm_socket_base#(DATA,PHASE) peer, int id = -1, string fname = "", int lineno = 0);
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null socket reference passed to tlm_bind of socket %s in file %s line %d", this.get_object_hiername(),fname,lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null socket reference passed to tlm_bind of socket %s", this.get_object_hiername()));
         return;
      end
      if((this.m_binding != null) && (peer.m_binding != null)) begin
         `vmm_error(log,`vmm_sformatf("Binding already exists for socket %s or %s.Binding request ignored.", this.get_object_hiername(),peer.get_object_hiername()));
         return;
      end
      this.m_binding = peer;
      peer.m_binding = this;
      this.peer_id = id;
      peer.peer_id = id;
   endfunction: tlm_bind

   function void tlm_import(vmm_tlm_socket_base#(DATA,PHASE) peer, string fname = "", int lineno = 0); 
      vmm_tlm_socket_base#(DATA,PHASE) child, parent;
      vmm_object _obj_peer, _obj_this; 
      if(peer == null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Null socket reference passed to tlm_import of socket %s, in file %s line %d", this.get_object_hiername(), fname, lineno));
         else
            `vmm_error(log,`vmm_sformatf("Null socket reference passed to tlm_import of socket %s", this.get_object_hiername()));
         return;
      end
      if(($cast(_obj_peer,peer.get_parent_object())) && ($cast(_obj_this, this.get_parent_object()))) begin
         if(_obj_this == _obj_peer.get_parent_object()) begin
            parent = this;
            child  = peer; 
         end  
         else if(_obj_this.get_parent_object() == _obj_peer) begin
            parent = peer;
            child  = this; 
         end
         else begin
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship, in file %s line %d",this.get_object_hiername() , peer.get_object_hiername(), fname, lineno));
            else   
               `vmm_error(log,`vmm_sformatf("Import is allowed only for parent child ports. Port %s and %s do not have a parent child relationship",this.get_object_hiername() , peer.get_object_hiername()));
            return;
         end
      end
      else begin
         if (log.start_msg(vmm_log::INTERNAL_TYP)) begin
            void'(log.text("Parent not defined.Please ensure tlm_import is called only for child_port.tlm_import(parent_port)")); 
            log.end_msg();
         end
         parent = peer;
         child = this;
      end     
      if(child.is_imported == 1) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Socket %s is already imported. Imported socket cannot be imported again, in file %s line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Socket %s is already imported. Imported socket cannot be imported again",child.get_object_hiername()));
         return;
      end
      if(child.m_binding != null) begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Socket %s has a binding. Bounded sockets cannot be imported, in file %s line %d",child.get_object_hiername(), fname, lineno));
         else   
            `vmm_error(log,`vmm_sformatf("Socket %s has a binding. Bounded sockets cannot be imported",child.get_object_hiername()));
         return;
      end
      child.parent_socket = parent;
      parent.child_socket = child;
      child.is_imported = 1;
   endfunction : tlm_import

   function void print_bindings();
      if(this.m_binding == null)
      begin
         if(this.parent_socket != null)
            `vmm_note(log,`vmm_sformatf("[Socket] %s (child) ---> [Socket] %s (parent)",this.get_object_hiername(), this.parent_socket.get_object_hiername()));
         else      
            `vmm_note(log,`vmm_sformatf("Socket %s is not bound to any Socket",this.get_object_hiername()));
         if(this.child_socket != null)
            `vmm_note(log,`vmm_sformatf("[Socket] %s (parent) <--- [Socket] %s (child)",this.get_object_hiername(), this.child_socket.get_object_hiername()));
      end   
      else
      begin
         `vmm_note(log,`vmm_sformatf("[Socket] %s <---> [Socket] %s",this.get_object_hiername(), this.m_binding.get_object_hiername()));
         if(this.child_socket != null)
            `vmm_note(log,`vmm_sformatf("[Socket] %s (parent) <--- [Socket] %s (child)",this.get_object_hiername(), this.child_socket.get_object_hiername()));
      end   
   endfunction: print_bindings

   function void check_bindings();
      if(this.m_binding == null)
      begin
         if(this.parent_socket == null)
            `vmm_warning(log,`vmm_sformatf("Socket %s is not bound to any Socket",this.get_object_hiername()));
      end   
   endfunction: check_bindings
   
   function void report_unbound();
      if(this.m_binding == null)
      begin
         if(this.parent_socket == null)
            `vmm_warning(log,`vmm_sformatf("Socket %s is not bound to any Socket",this.get_object_hiername()));
      end   
   endfunction: report_unbound

   function vmm_tlm_socket_base#(DATA,PHASE) get_peer();
      return this.m_binding;
   endfunction: get_peer

   function void tlm_unbind(string fname="", int lineno = 0);
      this.m_binding.peer_id = -1;
      this.peer_id = -1;
      this.m_binding.m_binding = null;
      this.m_binding = null;
   endfunction: tlm_unbind

   virtual function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log, "Virtual base class function nb_transport_fw is not extended");
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log, "Virtual base class function nb_transport_bw is not extended");
   endfunction 

   virtual task b_transport(DATA trans , ref int delay);
      `vmm_error(log, "Virtual base class task b_transport is not extended");
   endtask : b_transport
   
endclass: vmm_tlm_socket_base

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_initiator_socket#(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_socket_base#(DATA,PHASE);

   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_initiator_socket","class");
   /* local */ local INITIATOR m_parent;
   
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj,parent))? _obj: null , name , ((parent != null) && $cast(_obj,parent))? _obj.get_log(): null);
      this.m_parent = parent;
   endfunction

   virtual task b_transport(DATA trans, ref int delay);
      if(this.parent_socket == null)
         this.m_binding.b_transport(trans, delay);
      else
         this.parent_socket.b_transport(trans,delay);
   endtask : b_transport

   function vmm_tlm::sync_e nb_transport_fw(DATA trans,  ref PHASE ph, ref int delay);
      if(this.parent_socket == null)
         nb_transport_fw = this.m_binding.nb_transport_fw(trans, ph ,delay);
      else
         nb_transport_fw = this.parent_socket.nb_transport_fw(trans, ph ,delay);
   endfunction : nb_transport_fw
   
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay);
      if(this.child_socket == null) 
         nb_transport_bw = this.m_parent.nb_transport_bw(this.peer_id, trans, ph, delay);
      else
         nb_transport_bw = this.child_socket.nb_transport_bw(trans, ph, delay);
   endfunction : nb_transport_bw

endclass: vmm_tlm_initiator_socket

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_target_socket#(type TARGET = vmm_tlm_xactor, type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_socket_base#(DATA,PHASE);

   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_target_socket","class");
   /* local */ local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj,parent))? _obj:null , name,((parent != null ) && $cast(_obj,parent))? _obj.get_log(): null);
      this.m_parent = parent;
   endfunction: new

   virtual task b_transport(DATA trans, ref int delay);
      if(child_socket == null)
         this.m_parent.b_transport(this.peer_id , trans , delay );
      else
         this.child_socket.b_transport(trans , delay );
   endtask : b_transport

   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      if(child_socket == null)
         nb_transport_fw = this.m_parent.nb_transport_fw(this.peer_id, trans,  ph ,delay);
      else
         nb_transport_fw = this.child_socket.nb_transport_fw(trans,  ph ,delay);
   endfunction : nb_transport_fw
   
   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay);
      if(parent_socket == null)
         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph ,delay);
      else
         nb_transport_bw = this.parent_socket.nb_transport_bw(trans, ph ,delay);
   endfunction : nb_transport_bw

endclass: vmm_tlm_target_socket

//`ifdef VCS
//(* _vcs_vmm_class  = 1 *)
//`endif
//class vmm_tlm_nb_transport_port#(type INITIATOR = vmm_tlm_xactor, type DATA = vmm_data, type FW_PHASE = vmm_tlm::phase_e, type BW_PHASE = FW_PHASE) extends vmm_tlm_socket_base#(DATA,FW_PHASE);
//   /* local */ static local vmm_object _obj;
//   /* local */ local INITIATOR m_parent;
//   //vmm_log log = new("vmm_tlm_nb_transport_port","class"); 
//   function new(INITIATOR parent, string name);
//      super.new(($cast(_obj,parent))? _obj : null , name, (( parent != null) && $cast(_obj,parent))? _obj.get_log():null);
//      this.m_parent = parent;
//   endfunction
//
//   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref FW_PHASE ph, ref int delay);
//      if(parent_socket == null)
//         nb_transport_fw = this.m_binding.nb_transport_fw(trans, ph, delay);
//      else
//         nb_transport_fw = this.parent_socket.nb_transport_fw(trans, ph, delay);
//   endfunction : nb_transport_fw
//   
//   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref BW_PHASE ph, ref int delay);
//      if(child_socket == null)
//         nb_transport_bw = this.m_parent.nb_transport_bw(this.peer_id, trans, ph, delay);
//      else
//         nb_transport_bw = this.child_socket.nb_transport_bw( trans, ph, delay);
//   endfunction : nb_transport_bw
//
//endclass: vmm_tlm_nb_transport_port
//
//`ifdef VCS
//(* _vcs_vmm_class  = 1 *)
//`endif
//class vmm_tlm_nb_transport_export#(type TARGET = vmm_tlm_xactor, type DATA = vmm_data, type FW_PHASE = vmm_tlm::phase_e, type BW_PHASE = FW_PHASE) extends vmm_tlm_socket_base#(DATA,BW_PHASE);
//   /* local */ static local vmm_object _obj;
//   /* local */ local TARGET m_parent;
//   //vmm_log log = new("vmm_tlm_nb_transport_export","class");
//
//   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
//      super.new(($cast(_obj,parent))? _obj : null, name,((parent != null) && $cast(_obj,parent))?_obj.get_log(): null);
//      this.m_parent = parent;
//   endfunction: new
//
//   function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref BW_PHASE ph, ref int delay);
//      if(parent_socket == null)
//         nb_transport_bw = this.m_binding.nb_transport_bw(trans, ph, delay);
//      else
//         nb_transport_bw = this.parent_socket.nb_transport_bw(trans, ph, delay);
//   endfunction : nb_transport_bw
//
//   function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref FW_PHASE ph, ref int delay);
//      if(child_socket == null)
//         nb_transport_fw = this.m_parent.nb_transport_fw(this.peer_id, trans, ph, delay);
//      else
//         nb_transport_fw = this.child_socket.nb_transport_fw(trans, ph, delay);
//   endfunction : nb_transport_fw
//   
//endclass: vmm_tlm_nb_transport_export

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_tlm_reactive_if#(type DATA = vmm_data, int q_size = 1) extends vmm_object;
   typedef enum {BLOCKING, 
                 NONBLOCKING_FW,
                 NONBLOCKING
                 } m_method_e;
                 
   `VMM_LOG log = new("vmm_tlm_reactive_if","class");
   
   /* local */ protected vmm_tlm_b_transport_export#(vmm_tlm_reactive_if#(DATA,q_size),DATA) b_export;
   /* local */ protected vmm_tlm_nb_transport_fw_export#(vmm_tlm_reactive_if#(DATA,q_size),DATA, vmm_tlm::phase_e) nb_fw_export;
   /* local */ protected vmm_tlm_nb_transport_export#(vmm_tlm_reactive_if#(DATA,q_size),DATA, vmm_tlm::phase_e) nb_export[int];

   /* local */ protected DATA m_pending_data[$];
   /* local */ protected m_method_e m_method[$];
   /* local */ event trans_started;

   /* local */ protected int m_nb_id;
   /* local */ protected int m_in_process;
   /* local */ protected int m_b_pending;
   /* local */ protected int m_nb_id_q[$];
   local vmm_data _temp;
   
   function new(vmm_object parent, string name);
      super.new(parent,name);
      m_nb_id = 100000;
      m_b_pending = 0;
      m_in_process = 0;
   endfunction: new

   function int tlm_bind(vmm_tlm_base tlm_intf, vmm_tlm::intf_e intf, string fname = "", int lineno = 0);
      if(intf == vmm_tlm::TLM_NONBLOCKING_EXPORT)
      begin
         vmm_tlm_port_base#(DATA, vmm_tlm::phase_e) t_nb_port;
         if($cast(t_nb_port, tlm_intf)) begin
            nb_export[m_nb_id] = new(this, `vmm_sformatf("Non-Blocking Export%d",m_nb_id));
            nb_export[m_nb_id].tlm_bind(t_nb_port,m_nb_id);
            m_nb_id = m_nb_id + 1;
         end   
         else
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
            else   
               `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
      end
      else if(intf == vmm_tlm::TLM_BLOCKING_EXPORT)
      begin
         vmm_tlm_port_base#(DATA, vmm_tlm::phase_e) t_b_port;
         if($cast(t_b_port, tlm_intf)) begin
            if(b_export == null) begin
               b_export = new(this, "Blocking Export",100000); 
            end
            b_export.tlm_bind(t_b_port);
         end   
         else
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
            else   
               `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
      end
      else if(intf == vmm_tlm::TLM_NONBLOCKING_FW_EXPORT)
      begin
         vmm_tlm_port_base#(DATA, vmm_tlm::phase_e) t_nb_fw_port;
         if($cast(t_nb_fw_port, tlm_intf)) begin
            if(nb_fw_export == null) begin
               nb_fw_export = new(this, "Non-Blocking FW Export",100000);
            end
            nb_fw_export.tlm_bind(t_nb_fw_port);
         end
         else
            if(fname != "" && lineno != 0)
               `vmm_error(log,`vmm_sformatf("Channel interface and TLM interface are not not matching interfaces, in file %s line %d", fname, lineno));
            else   
               `vmm_error(log,"Channel interface and TLM interface are not not matching interfaces");
      end
      else
      begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,`vmm_sformatf("Wrong type is passed as a second argument to tlm_bind method, in file %s line %d", fname, lineno));
         else   
            `vmm_error(log,"Wrong type is passed as a first argument to tlm_bind method");
      end
   endfunction: tlm_bind

   task b_transport(int id = -1, DATA trans, ref int delay);
      int _trans_num = m_pending_data.size();
      if(_trans_num < q_size) begin
         m_pending_data.push_back(trans);
         m_method.push_back(BLOCKING);
         ->trans_started;
`ifndef VMM_DATA_NO_NOTIFY_ALL
         if($cast(_temp,trans))
            _temp.notify.wait_for(vmm_data::ENDED);
`endif // VMM_DATA_NO_NOTIFY_ALL
      end
      else begin
      end
   endtask : b_transport

   function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, ref vmm_tlm::phase_e ph, ref int delay); 
      int _trans_num = m_pending_data.size();
      if(_trans_num < q_size) begin
         if(id > 99999) begin
            m_pending_data.push_back(trans);
            m_method.push_back(NONBLOCKING);
            m_nb_id_q.push_back(id);
            ->trans_started;
            return vmm_tlm::TLM_ACCEPTED;
         end
         else begin
            m_pending_data.push_back(trans);
            m_method.push_back(NONBLOCKING_FW);
            ->trans_started;
            return vmm_tlm::TLM_ACCEPTED;
         end
      end
      else begin
         return vmm_tlm::TLM_REFUSED;
      end
   endfunction : nb_transport_fw
   
   function DATA try_get();
      if(m_pending_data.size() != 0) begin
         if(m_in_process == 0) begin
            try_get = m_pending_data[0];
            m_in_process = 1;
         end
         else begin
            `vmm_error(log,"Previously activated transaction is not complete, do complete before trying to get(try_get) next transaction");
         end
      end
      else begin
         return null;
      end
   endfunction: try_get

   task get(output DATA tr);
      if(m_in_process == 0) begin
         if(m_pending_data.size() == 0) begin
            @trans_started;
         end
         tr = m_pending_data[0];
         m_in_process = 1;
      end
      else begin
         `vmm_error(log,"Previously activated transaction is not complete, do complete before trying to get next transaction");
      end
   endtask: get

   function void completed();
      DATA tr = m_pending_data.pop_front();
      if(m_method[0] == BLOCKING) begin
`ifndef VMM_DATA_NO_NOTIFY_ALL
         if($cast(_temp,tr))
            _temp.notify.indicate(vmm_data::ENDED);
`endif // VMM_DATA_NO_NOTIFY_ALL
      end
      else if(m_method[0] == NONBLOCKING) begin
         vmm_tlm::phase_e ph;
         int del;
         ph = vmm_tlm::END_RESP;
`ifndef VMM_DATA_NO_NOTIFY_ALL
         if($cast(_temp,tr))
            _temp.notify.indicate(vmm_data::ENDED);
`endif // VMM_DATA_NO_NOTIFY_ALL
         nb_export[m_nb_id_q.pop_front()].nb_transport_bw(tr,ph,del); 
      end
      else if(m_method[0] == NONBLOCKING_FW) begin
`ifndef VMM_DATA_NO_NOTIFY_ALL
         if($cast(_temp,tr))
            _temp.notify.indicate(vmm_data::ENDED);
`endif // VMM_DATA_NO_NOTIFY_ALL
      end
      m_in_process = 0;
      m_method.delete(0);
   endfunction: completed

endclass: vmm_tlm_reactive_if

// Extern methods
function void vmm_tlm::print_bindings(vmm_object root = null);
   vmm_tlm_base _this_obj;
   vmm_object _this_temp_obj;
   string root_name = "";
   for(int i = 0 ; i < root.get_num_children();i++) begin
      if($cast(_this_temp_obj, root.get_nth_child(i))) begin
         if($cast(_this_obj, root.get_nth_child(i)))
             _this_obj.print_bindings();
         else if(_this_temp_obj.get_num_children() > 0)
            print_bindings(root.get_nth_child(i));
      end      
   end       
endfunction: print_bindings

function void vmm_tlm::check_bindings(vmm_object root = null);
   vmm_tlm_base _this_obj;
   vmm_object _this_temp_obj;
   for(int i = 0 ; i < root.get_num_children();i++) begin
      if($cast(_this_temp_obj, root.get_nth_child(i))) begin
         if($cast(_this_obj, root.get_nth_child(i)))
             _this_obj.check_bindings();
         else if(_this_temp_obj.get_num_children() > 0)
            check_bindings(root.get_nth_child(i));
      end      
   end       
endfunction: check_bindings

function void vmm_tlm::report_unbound(vmm_object root = null);
   vmm_tlm_base _this_obj;
   vmm_object _this_temp_obj;
   for(int i = 0 ; i < root.get_num_children();i++) begin
      if($cast(_this_temp_obj, root.get_nth_child(i))) begin
         if($cast(_this_obj, root.get_nth_child(i)))
             _this_obj.report_unbound();
         else if(_this_temp_obj.get_num_children() > 0)
            report_unbound(root.get_nth_child(i));
      end      
   end
endfunction: report_unbound

//vmm_tlm_transport_interconnect_base
class vmm_tlm_transport_interconnect_base #(type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_object;
   `VMM_LOG log = new("vmm_tlm_transport_interconnect_base","class");

   /* local */ protected vmm_tlm_b_transport_export#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA) b_export;
   /* local */ protected vmm_tlm_nb_transport_export#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA, PHASE) nb_export;
   /* local */ protected vmm_tlm_nb_transport_fw_export#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA, PHASE) nb_fw_export;

   /* local */ protected vmm_tlm_b_transport_port#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA) b_port;
   /* local */ protected vmm_tlm_nb_transport_port#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA, PHASE) nb_port;
   /* local */ protected vmm_tlm_nb_transport_fw_port#(vmm_tlm_transport_interconnect_base#(DATA,PHASE),DATA, PHASE) nb_fw_port;
   
   /* local */ protected vmm_tlm_export_base#(DATA, PHASE) t_b_export;
   /* local */ protected vmm_tlm_export_base#(DATA, PHASE) t_nb_export;              
   /* local */ protected vmm_tlm_export_base#(DATA, PHASE) t_nb_fw_export;

   /* local */ protected vmm_tlm_port_base#(DATA, PHASE) t_b_port;
   /* local */ protected vmm_tlm_port_base#(DATA, PHASE) t_nb_port;
   /* local */ protected vmm_tlm_port_base#(DATA, PHASE) t_nb_fw_port;

   /* local */ DATA pending_data[$];
   /* local */ event nb_start_event;
   /* local */ event b_comp_event;
   /* local */ event b_start_event;
   /* local */ PHASE m_ph[$];
   /* local */ int m_delay[$];
   /* local */ int is_bound;
   /* local */ int is_fw;

   function new(vmm_object parent, string name);
      super.new(parent,name);
      is_bound = 0;
      is_fw = 0;
   endfunction: new

   function int tlm_bind(vmm_tlm_base tlm_intf_port, vmm_tlm_base tlm_intf_export, vmm_tlm::intf_e intf, string fname = "", int lineno = 0);
      int _temp_check = 0;
      if(is_bound == 0) begin
         case(intf)
            vmm_tlm::TLM_NONBLOCKING_EXPORT: begin
               if($cast(t_nb_export, tlm_intf_export)) begin
                  if($cast(t_b_port, tlm_intf_port)) begin
                     b_export = new(this, "Blocking Export",100000);
                     nb_port = new(this, "Non-Blocking Port");
                     t_b_port.tlm_bind(b_export);
                     t_nb_export.tlm_bind(nb_port);
                     is_bound = 1;
                     fork
                        tlm_b_port_proc();  
                     join_none
                  end   
               end
            end
            vmm_tlm::TLM_NONBLOCKING_PORT: begin
               if($cast(t_nb_port, tlm_intf_port)) begin
                  if($cast(t_b_export, tlm_intf_export)) begin
                     nb_export = new(this, "Non-Blocking Export",1000);
                     b_port = new(this, "Blocking Port");
                     t_nb_port.tlm_bind(nb_export);
                     t_b_export.tlm_bind(b_port);
                     is_bound = 1;
                     fork
                        tlm_nb_port_proc();  
                     join_none
                  end
               end
            end
            vmm_tlm::TLM_NONBLOCKING_FW_EXPORT: begin
               if($cast(t_nb_fw_export, tlm_intf_export)) begin
                  if($cast(t_b_port, tlm_intf_port)) begin
                     b_export = new(this, "Blocking Export",100000);
                     nb_fw_port = new(this, "Non-Blocking FW Port");
                     t_b_port.tlm_bind(b_export);
                     t_nb_fw_export.tlm_bind(nb_fw_port);
                     is_bound = 1;
                     is_fw = 1;
                     fork
                        tlm_b_port_proc();  
                     join_none
                  end   
               end
            end
            vmm_tlm::TLM_NONBLOCKING_FW_PORT: begin
               if($cast(t_nb_fw_port, tlm_intf_port)) begin
                  if($cast(t_b_export, tlm_intf_export)) begin
                     nb_fw_export = new(this, "Non-Blocking FW Export",1000);
                     b_port = new(this, "Blocking Port");
                     t_nb_fw_port.tlm_bind(nb_fw_export);
                     t_b_export.tlm_bind(b_port);
                     is_bound = 1;
                     is_fw = 1;
                     fork
                        tlm_nb_port_proc();  
                     join_none
                  end
               end
            end
	    default: begin
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Wrong type is passed as a third argument to tlm_bind method in vmm_tlm_transport_interconnect, valid values are TLM_NONBLOCKING_EXPORT, TLM_NONBLOCKING_PORT, TLM_NONBLOCKING_FW_PORT and TLM_NONBLOCKING_FW_EXPORT, in file %s line %d", fname, lineno));
               else   
                  `vmm_error(log,"Wrong type is passed as a third argument to tlm_bind method in vmm_tlm_transport_interconnect, valid values are TLM_NONBLOCKING_EXPORT, TLM_NONBLOCKING_PORT, TLM_NONBLOCKING_FW_PORT and TLM_NONBLOCKING_FW_EXPORT");
               _temp_check = 1;
            end
         endcase
         if((!is_bound) && (!_temp_check) ) begin
               if(fname != "" && lineno != 0)
                  `vmm_error(log,$psprintf("Interconnect interface and TLM interface dont match interfaces, in file %s line %d", fname, lineno));
               else
                  `vmm_error(log,"Interconnect interface and TLM interface dont match interfaces");
         end
      end
      else begin
         if(fname != "" && lineno != 0)
            `vmm_error(log,$psprintf("Interface in the interconnect is already bound, in file %s line %d", fname, lineno));
         else
            `vmm_error(log,"Interface in the interconnect is already bound");
      end
   endfunction: tlm_bind

   virtual task b_transport(int id = -1, DATA trans, ref int delay);
   begin   
      pending_data.push_back(trans);
      m_delay.push_back(delay);
      ->b_start_event;
      @b_comp_event;
      void'(pending_data.pop_front());
      delay = m_delay.pop_front();
   end   
   endtask : b_transport

   local task tlm_b_port_proc();
   begin
      forever 
      begin
         @b_start_event;
         fork
            begin
               DATA cur_data = pending_data[$];
               PHASE cur_ph;
               int cur_delay = m_delay[$];
               vmm_tlm::sync_e m_sync_e;
               if(is_fw == 1)
               begin
                  m_sync_e = nb_fw_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
                  m_delay[$] = cur_delay;
                  ->b_comp_event;
               end
               else
               begin
                  m_sync_e = nb_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
               end
            end
         join_none
      end
   end
   endtask: tlm_b_port_proc

   virtual function vmm_tlm::sync_e nb_transport_bw(int id = -1, DATA trans, ref PHASE ph, ref int delay); 
   begin
      int data_que[$], ph_que[$];
      DATA t_data;
      data_que = pending_data.find_first_index(t_data) with (t_data == trans);
      if(data_que.size() == 0 ) 
      begin
         `vmm_note(log,"Transaction received on backward path does not match any pending transaction sent on forward path");
      end
      else 
      begin
         m_delay[$] = delay;
         ->b_comp_event;
         return vmm_tlm::TLM_COMPLETED;
      end   
   end
   endfunction : nb_transport_bw

   virtual function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, ref PHASE ph, ref int delay); 
   begin
      pending_data.push_back(trans);
      m_ph.push_back(ph);
      m_delay.push_back(delay);
      ->nb_start_event;
      return vmm_tlm::TLM_COMPLETED;
   end
   endfunction : nb_transport_fw

   local task tlm_nb_port_proc();
   begin
      forever
      begin
         @nb_start_event;
         fork
         begin
            DATA cur_data = pending_data[$];
            int data_que[$], ph_que[$];
            int delay = m_delay[$];
            PHASE cur_ph = m_ph[$];
            DATA t_data;
            
            if(is_fw == 1)
            begin
               b_port.b_transport(cur_data, delay);
               
               data_que = pending_data.find_first_index(t_data) with (t_data == cur_data);
               ph_que = m_ph.find_first_index(t_ph) with (t_ph == cur_ph);
               if(data_que.size() != 0)
               begin
                  pending_data.delete(data_que[0]);
                  m_delay.delete(data_que[0]);
               end   
               if(ph_que.size() != 0)
                  m_ph.delete(ph_que[0]);
            end
            else
            begin
               b_port.b_transport(cur_data, delay);
               
               nb_export.nb_transport_bw(cur_data,cur_ph,delay);

               data_que = pending_data.find_first_index(t_data) with (t_data == cur_data);
               ph_que = m_ph.find_first_index(t_ph) with (t_ph == cur_ph);
               if(data_que.size() != 0)
               begin
                  pending_data.delete(data_que[0]);
                  m_delay.delete(data_que[0]);
               end   
               if(ph_que.size() != 0)
                  m_ph.delete(ph_que[0]);
            end   
         end
         join_none
      end
   end
   endtask: tlm_nb_port_proc

endclass: vmm_tlm_transport_interconnect_base

//vmm_tlm_transport_interconnect
class vmm_tlm_transport_interconnect #(type DATA = vmm_data) extends vmm_tlm_transport_interconnect_base#(DATA);

   function new(vmm_object parent, string name);
      super.new(parent,name);
      is_bound = 0;
      is_fw = 0;
   endfunction: new

   task b_transport(int id = -1, DATA trans, ref int delay);
   begin   
      pending_data.push_back(trans);
      m_delay.push_back(delay);
      ->b_start_event;
      @b_comp_event;
      pending_data.pop_front();
      delay = m_delay.pop_front();
   end   
   endtask : b_transport

   local task tlm_b_port_proc();
   begin
      forever 
      begin
         @b_start_event;
         fork
            begin
               DATA cur_data = pending_data[$];
               vmm_tlm::phase_e cur_ph = vmm_tlm::BEGIN_REQ;
               int cur_delay = m_delay[$];
               vmm_tlm::sync_e m_sync_e;
               if(is_fw == 1)
               begin
                  m_sync_e = nb_fw_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
                  m_delay[$] = cur_delay;
                  ->b_comp_event;
               end
               else
               begin
                  m_sync_e = nb_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
                  case(m_sync_e)
                     vmm_tlm::TLM_ACCEPTED: begin
                     end
                     vmm_tlm::TLM_UPDATED: begin
                        if(cur_ph == vmm_tlm::END_REQ)
                        begin
                        end
                        else if(cur_ph == vmm_tlm::BEGIN_RESP)
                        begin
                          cur_ph = vmm_tlm::END_RESP;
                          nb_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
                          m_delay[$] = cur_delay;
                          ->b_comp_event;
                        end
                     end
                     vmm_tlm::TLM_COMPLETED: begin
                        ->b_comp_event;
                     end
                  endcase
               end
            end
         join_none
      end
   end
   endtask: tlm_b_port_proc

   function vmm_tlm::sync_e nb_transport_bw(int id = -1, DATA trans, ref vmm_tlm::phase_e ph, ref int delay); 
   begin
      int data_que[$], ph_que[$];
      DATA t_data;
      data_que = pending_data.find_first_index(t_data) with (t_data == trans);
      if(data_que.size() == 0 ) 
      begin
         `vmm_note(log,"Transaction received on backward path does not match any pending transaction sent on forward path");
      end
      else 
      begin
         if(ph == vmm_tlm::END_REQ)
         begin
            return vmm_tlm::TLM_ACCEPTED;
         end
         else if(ph == vmm_tlm::BEGIN_RESP)
         begin
            m_delay[$] = delay;
            ->b_comp_event;
            ph = vmm_tlm::END_RESP;
            return vmm_tlm::TLM_UPDATED;
         end
         else
         begin
            `vmm_error(log,"Wrong phase passed to nb_transport_bw, valid values are END_REQ and BEGIN_RESP"); 
         end
      end   
   end
   endfunction : nb_transport_bw

   function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, ref vmm_tlm::phase_e ph, ref int delay); 
   begin
      if(is_fw == 1)
      begin
         if(ph == vmm_tlm::BEGIN_REQ)
         begin
            pending_data.push_back(trans);
            m_ph.push_back(ph);
            m_delay.push_back(delay);
            ->nb_start_event;
            ph = vmm_tlm::BEGIN_RESP;
            return vmm_tlm::TLM_UPDATED;
         end
         else if(ph == vmm_tlm::END_RESP)
         begin
            return vmm_tlm::TLM_COMPLETED;
         end
         else
         begin
            `vmm_error(log,"Wrong phase passed to nb_transport_fw, valid values are BEGIN_REQ and END_RESP"); 
         end
      end
      else
      begin
         if(ph == vmm_tlm::BEGIN_REQ)
         begin
            pending_data.push_back(trans);
            m_ph.push_back(ph);
            m_delay.push_back(delay);
            ->nb_start_event;
            return vmm_tlm::TLM_ACCEPTED;
         end
         else if(ph == vmm_tlm::END_RESP)
         begin
            return vmm_tlm::TLM_COMPLETED;
         end
         else
         begin
            `vmm_error(log,"Wrong phase passed to nb_transport_fw, valid values are BEGIN_REQ and END_RESP"); 
         end
      end
   end
   endfunction : nb_transport_fw

   local task tlm_nb_port_proc();
   begin
      forever
      begin
         @nb_start_event;
         fork
         begin
            DATA cur_data = pending_data[$];
            int data_que[$], ph_que[$];
            int delay = m_delay[$];
            vmm_tlm::phase_e cur_ph = m_ph[$];
            DATA t_data;
            
            if(is_fw == 1)
            begin
               b_port.b_transport(cur_data, delay);
               
               data_que = pending_data.find_first_index(t_data) with (t_data == cur_data);
               ph_que = m_ph.find_first_index(t_ph) with (t_ph == cur_ph);
               if(data_que.size() != 0)
               begin
                  pending_data.delete(data_que[0]);
                  m_delay.delete(data_que[0]);
               end   
               if(ph_que.size() != 0)
                  m_ph.delete(ph_que[0]);
            end
            else
            begin
               b_port.b_transport(cur_data, delay);
               
               cur_ph = vmm_tlm::BEGIN_RESP;
               nb_export.nb_transport_bw(cur_data,cur_ph,delay);

               data_que = pending_data.find_first_index(t_data) with (t_data == cur_data);
               ph_que = m_ph.find_first_index(t_ph) with (t_ph == cur_ph);
               if(data_que.size() != 0)
               begin
                  pending_data.delete(data_que[0]);
                  m_delay.delete(data_que[0]);
               end   
               if(ph_que.size() != 0)
                  m_ph.delete(ph_que[0]);
            end   
         end
         join_none
      end
   end
   endtask: tlm_nb_port_proc

endclass: vmm_tlm_transport_interconnect
