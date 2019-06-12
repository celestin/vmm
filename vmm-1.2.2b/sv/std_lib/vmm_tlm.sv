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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm
// 
// This class contains the sync_e enumerated for various phases of 
// the transaction. All TLM port classes use this enumerated value as 
// the default template for defining the phases of the transaction. 
//------------------------------------------------------------------------------
class vmm_tlm;
   typedef enum {ILLEGAL_TYPE = -1,
   				 TLM_REFUSED, 
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

   //------------------------------------------------------------------------------
   // FUNCTION: print_bindings
   // 
   // Prints the bindings of all TLM ports and exports, including transport 
   // ports and exports, sockets and analysis ports, and exports 
   // instantiated under the <vmm_object>, specified by the root argument. 
   // If null is passed, then the bindings are printed for all TLM ports and 
   // exports in the environment. 
   // 
   // The print_bindings() method is also available with all TLM 
   // ports and exports, and can be invoked for the particular port object. 
   //------------------------------------------------------------------------------
   extern static function void print_bindings(vmm_object root = null);

   //------------------------------------------------------------------------------
   // FUNCTION: check_bindings
   // 
   // A warning is generated if a port is unbound ,or if an export contains 
   // less than the minimum bindings specified for the export. Analysis 
   // port bindings are reported with debug severity. If root is not specified, 
   // then the binding checks are done for all TLM ports and exports in the 
   // environment. 
   // 
   // The check_bindings() method is also available with all TLM 
   // ports and exportsm and can be invoked for the particular port object. 
   //------------------------------------------------------------------------------
   extern static function void check_bindings(vmm_object root = null);

   //------------------------------------------------------------------------------
   // FUNCTION: report_unbound
   // 
   // Reports all unbound TLM ports and exports, including transport ports 
   // and exports, sockets and analysis ports, and exports instantiated 
   // under the <vmm_object>, specified by the root argument. If null is 
   // passed, then the bindings are printed for all TLM ports and exports 
   // in the environment. 
   // 
   // A warning is generated, if any TLM port or export under the specified 
   // root is left unbound. For analysis ports, a message with debug 
   // severity is generated. 
   // 
   // The report_unbound() method is also available with all TLM 
   // ports and exports, and can be invoked for the particular port object. 
   //------------------------------------------------------------------------------
   extern static function void report_unbound(vmm_object root = null);
endclass: vmm_tlm

typedef class vmm_rw_access;
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif


//------------------------------------------------------------------------------
// CLASS: vmm_tlm_extension_base
// 
// Generic payload extensions base class. This class must be 
// extended to define user extensions of the 
// <vmm_tlm_generic_payload> class. 
//------------------------------------------------------------------------------
class vmm_tlm_extension_base extends vmm_data;
   `vmm_data_new(vmm_tlm_extension_base)

   virtual function vmm_tlm_extension_base clone();
      `vmm_error(log,"Virtual base class function clone is not extended.");
	  return(null);
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


//------------------------------------------------------------------------------
// CLASS: vmm_tlm_generic_payload
// 
// This data class contains attributes, as defined by the OSCI TLM2.0 
// tlm_generic_payload class. The class is extended from the 
// <vmm_rw_access> class, which is in turn extended from <vmm_data> 
// class. The SystemVerilog implementation uses the VMM data 
// shorthand macros, to implement all methods that are implemented 
// by the <vmm_data> class. 
// 
// Generic payload class can be extended to have user defined 
// functionality by extending vmm_tlm_extension_base. The 
// <vmm_tlm_generic_payload> class has a dynamic array of 
// <vmm_tlm_extension_base>, which is used to store the user 
// extensions. 
//------------------------------------------------------------------------------
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
    

   //------------------------------------------------------------------------------
   // FUNCTION: set_extension
   // 
   // This function is used to assign the extension base to the dynamic 
   // array in the generic payload class at the specified index, and returns 
   // the old extension at that index. 
   //------------------------------------------------------------------------------
   function vmm_tlm_extension_base set_extension(int index, vmm_tlm_extension_base ext);
     vmm_tlm_extension_base tmp = m_extensions[index];
     $cast(m_extensions[index], ext);
     set_extension = tmp;
   endfunction: set_extension
   

   //------------------------------------------------------------------------------
   // FUNCTION: get_extension
   // 
   // Returns the user-defined extension at the specified index from the 
   // extensions array of the generic payload class. 
   //------------------------------------------------------------------------------
   function vmm_tlm_extension_base get_extension(int index);
     get_extension = m_extensions[index];
   endfunction: get_extension
   

   //------------------------------------------------------------------------------
   // FUNCTION: clear_extension
   // 
   // This function is used to clear the extension from the dynamic array 
   // in the generic payload class in that index. 
   //------------------------------------------------------------------------------
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
       m_length>=min_m_length;          }
   constraint c_data_size_reasonable
     { m_length<=max_m_length;          }
   constraint c_byte_enable_valid
     { m_byte_enable.size == m_byte_enable_length; 
       m_byte_enable_length>=min_m_byte_enable_length; }
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
virtual class vmm_tlm_xactor #(type DATA=vmm_data, type PHASE=vmm_tlm::phase_e) extends vmm_xactor;

   function new(string name="", string inst="");
      super.new(name,inst);
   endfunction: new

   virtual function vmm_tlm::sync_e nb_transport_fw(int id = -1, DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_fw is not extended."); 
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(int id = -1, DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction 

   virtual task b_transport(int id = -1, DATA trans,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport

   virtual function void write(int id = -1, DATA trans);
      `vmm_error(log,"Virtual base class function write is not extended."); 
   endfunction : write
endclass: vmm_tlm_xactor


typedef class vmm_tlm_export_base;
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_port_base
// 
// Abstract base class for all TLM2.0 transport ports 
//------------------------------------------------------------------------------
virtual class vmm_tlm_port_base #(type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_base;

   `VMM_LOG log;
   /* local */ protected vmm_tlm_export_base#(DATA,PHASE) m_binding; 

   /* local */ protected int peer_id = -1; 

   /* local */ protected vmm_tlm_port_base#(DATA,PHASE) parent_port;
   /* local */ protected vmm_tlm_port_base#(DATA,PHASE) child_port;
   /* local */ bit is_imported = 0; 
   /* local */ bit is_nb = 0; 
   

   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent, if the base class extends <vmm_object>. Sets the 
   // name of the instance. log is the message interface instance to be 
   // used for reporting messages. 
   //------------------------------------------------------------------------------
   function new(vmm_object parent, string name , `VMM_LOG log);
      super.new(parent,name);
      if(log == null) begin
         this.log = new("vmm_tlm_port_base","class");
      end
      else
         this.log = log;
   endfunction: new
  

   //------------------------------------------------------------------------------
   // FUNCTION: tlm_bind
   // 
   // Binds the TLM port to the TLM export passed as an argument. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_import
   // 
   // This is a special port-to-port binding. It simplifies the binding for 
   // hierarchical ports and exports, by making the inner port visible to the 
   // outer hierarchy. The binding finally resolves to a port-export binding. 
   // 
   // The method allows only parent-child ports to be imported. An error 
   // is generated, if the ports do not share a parent-child relationship. It 
   // is an error to import a port that is already imported. It is an error to 
   // import a port that is already bound. 
   // 
   // The method can be called for both parent-to-child binding and 
   // child-to-parent binding. The parent transactors must be derivatives 
   // of <vmm_object>. If the parent is a <vmm_xactor> extension, then the 
   // <vmm_xactor> base class should be underpinned. If the 
   // <vmm_xactor> is not underpinned, or the parent is not a derivative of 
   // <vmm_object>, then only 
   // child.port.tlm_import(parent.port) is allowed. The error 
   // checks are not executed, and you must ensure legal connections. 
   // The fname and lineno arguments are used to track the file name 
   // and the line number, where tlm_import is invoked from. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: get_peer
   // 
   // Returns the export bound to the current port. Returns Null, if the port 
   // does not contain a binding. 
   //------------------------------------------------------------------------------
   function vmm_tlm_export_base#(DATA,PHASE) get_peer();
      return this.m_binding;
   endfunction: get_peer


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_unbind
   // 
   // Sets the port binding to null. Also, removes the current port 
   // descriptors binding from the export that the port is bound to. A 
   // warning is generated if a binding does not exist for this port. 
   // 
   // This method can be used to dynamically change existing bindings for 
   // a port. The fnameand lineno arguments are used to track the file 
   // name and the line number, where tlm_unbind is invoked from. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: get_peer_id
   // 
   // Returns the id of this port, with respect to its export binding. If port 
   // is not bound, -1 is returned. 
   //------------------------------------------------------------------------------
   function int get_peer_id();
      return this.peer_id;
   endfunction : get_peer_id

   /* local */ function void unbind_peer();
      this.m_binding = null;
      this.peer_id = -1;
   endfunction : unbind_peer 

   virtual function vmm_tlm::sync_e nb_transport_fw(DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log,"Virtual base class function nb_transport_fw is not extended."); 
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay, input int id = -1);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction 

   virtual task b_transport(DATA trans,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport
   
endclass: vmm_tlm_port_base
   
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_export_base
// 
// Abstract base class for all TLM2.0 transport exports. This class 
// contain the methods that are required by all TLM2.0 transport export 
// implementations. Any user-defined export must be extended from 
// this base class. 
// 
// The parameter DATA is the type of the transaction object of the 
// export services. The default type is <vmm_data>. The parameter 
// PHASE is the type of the phasing class. The default value is 
// vmm_tlm::phase_e. 
//------------------------------------------------------------------------------
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

   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent, if it is an extension of <vmm_object>. Sets the name 
   // of the instance. Sets the maximum and minimum bindings allowed 
   // for this export. log is the message interface instance to be used for 
   // reporting messages. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_bind
   // 
   // Binds the TLM export to the TLM port passed as an argument. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_import
   // 
   // This is a special way of exporting bindings. It simplifies the binding 
   // for hierarchical exports, by making the inner export visible to the 
   // outer hierarchy. The binding resolves to a port-export binding. The 
   // method allows only parent-child exports to be imported. An error is 
   // generated, if the exports do not share a parent-child relationship. It 
   // is an error to import an export that is already imported. It is an error 
   // to import an export that is already bound. The method can be called 
   // for both parent-to-child bindings and child-to-parent bindings. For 
   // this, the parent transactors must be derivatives of <vmm_object>. If 
   // the parent is a <vmm_xactor>, then the <vmm_xactor> 
   // class should be underpinned. If the <vmm_xactor> is not 
   // underpinned, or the parent is not a derivative of <vmm_object>, then 
   // only child.export.tlm_import(parent.export)is allowed. 
   // The error checks are not executed, and you must ensure legal 
   // connections. 
   // 
   // The fname and lineno arguments are used to track the file name 
   // and the line number, where the tlm_import is invoked from. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: get_n_peers
   // 
   // Returns the number of port export bindings, as set with the 
   // tlm_bind() method. 
   //------------------------------------------------------------------------------
   function int get_n_peers();
      return this.m_bindings;
   endfunction : get_n_peers


   //------------------------------------------------------------------------------
   // FUNCTION: get_peers
   // 
   // Returns the queue of bindings of the export in the specified queue. 
   //------------------------------------------------------------------------------
   function void get_peers(output vmm_tlm_port_base#(DATA,PHASE) peers[$]);
      peers = this.bindings;
   endfunction : get_peers


   //------------------------------------------------------------------------------
   // FUNCTION: get_peer_id
   // 
   // Returns the binding id of the specified port bound to this export. If 
   // the specified port is not bound to this export, then -1 is returned. 
   //------------------------------------------------------------------------------
   function int get_peer_id(vmm_tlm_port_base#(DATA,PHASE) peer);
      if(peer == null) begin
         `vmm_error(log,`vmm_sformatf("Null port reference passed to get_peer_id of export %s", this.get_object_hiername()));
      end
      return peer.get_peer_id();
   endfunction : get_peer_id


   //------------------------------------------------------------------------------
   // FUNCTION: get_peer
   // 
   // Returns the port bound to the current export, with the specified id. 
   // Null is returned, if the port does not have a binding with the specified 
   // id. If only one binding exists for the export, then the handle to be 
   // binding is returned without considering the id value passed. 
   //------------------------------------------------------------------------------
   function vmm_tlm_port_base#(DATA,PHASE) get_peer(int id = -1);
      if(this.bindings.size() == 1)
         return this.bindings[0];
      else if(id < 0 ) begin 
         `vmm_warning(log,`vmm_sformatf("Invalid id %d specfied for transport export %s get_peer method.Positive id is required",id, this.get_object_hiername()));
      end
      else 
         return this.bindings_id[id];
   endfunction : get_peer


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_unbind
   // 
   // Removes the binding supplied as a peer or id from the list of 
   // bindings, for this export. Also, removes the binding of this export with 
   // the connected port. 
   // 
   // If the supplied peer is not null, then the binding of the peer is 
   // removed. An error is generated, if the supplied peeris not bound to 
   // this export. 
   // 
   // If the supplied peeris null and the supplied id is a positive number, 
   // then the binding to the port with the supplied idis removed. An error 
   // is generated, if there is no binding with the supplied positive id. 
   // 
   // If the supplied peer is null and the supplied id negative, then all 
   // bindings for this export are removed. 
   // 
   // On unbinding, the id of the unbound port becomes available for 
   // reuse. 
   // 
   // The fnameand lineno arguments are used to track the file name 
   // and the line number, where the tlm_unbind is invoked from. 
   //------------------------------------------------------------------------------
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
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans,  ref PHASE ph, ref int delay, input int id = -1);
      `vmm_error(log,"Virtual base class function nb_transport_bw is not extended."); 
	  return (vmm_tlm::ILLEGAL_TYPE);
   endfunction 

   virtual task b_transport(int id = -1, DATA trans ,ref int delay);
      `vmm_error(log,"Virtual base class task b_transport is not extended."); 
   endtask : b_transport
   
endclass: vmm_tlm_export_base
   
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_b_transport_port
// 
// Base class for modeling a blocking transport port. 
//------------------------------------------------------------------------------
class vmm_tlm_b_transport_port #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data) extends vmm_tlm_port_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_b_transport_port","class");


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent and instance name of the blocking transport port. 
   //------------------------------------------------------------------------------
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null);
   endfunction: new


   //------------------------------------------------------------------------------
   // TASK: b_transport
   // 
   // TLM task for blocking transport. Invokes the ~b_transport()~ 
   // method of the bounded export. The index argument can be used 
   // for associating the b_transport call with the caller, this can be 
   // usefull for the target to identify which producers called this task. The 
   // trans argument is a handle of the transaction object. The delay 
   // argument is the timing annotation. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_b_transport_export
// 
// Blocking transport export class. 
// 
// Any class instantiating this blocking transport export, must provide 
// an implementation of the b_transport() task. 
//------------------------------------------------------------------------------
class vmm_tlm_b_transport_export #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data) extends vmm_tlm_export_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_b_transport_export","class");
   /* local */ local TARGET m_parent;


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent and instance name of the blocking transport export. 
   // Sets the maximum and minimum bindings allowed for this export. 
   // The default value of maximum bindings is 1, and the minimum 
   // binding is 0. An error is generated during ~tlm_bind()~, if the current 
   // binding exceeds the maximum allowed bindings for the export. An 
   // error is generated during elaboration, if the export does not contain 
   // the minimum number of specified bindings. 
   //------------------------------------------------------------------------------
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds, ((parent != null ) && $cast(_obj,parent))? _obj.get_log() : null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_b_transport_export constructor");
      this.m_parent = parent;
   endfunction: new


   //------------------------------------------------------------------------------
   // TASK: b_transport
   // 
   // Blocking transport task of the transport export. This task is internally 
   // called by the bound transport port. This task calls the 
   // b_transport() method of the parent transactor in which it is 
   // instantiated. 
   // 
   // The specified trans argument is a handle of the transaction object, 
   // id specifies the binding identifier of this export, delay argument is 
   // the timing annotation. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_fw_port
// 
// Non-blocking transport port for the forward path. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_fw_port #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_fw_port","class");

   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent and instance name of the non-blocking forward 
   // transport port. 
   //------------------------------------------------------------------------------
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ?_obj.get_log() : null);
      this.is_nb = 1;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: nb_transport_fw
   // 
   // Call the ~nb_transport_fw()~ method of the bound export. The 
   // argument, trans is a handle of the transaction object, phis a handle 
   // of the phase class, and delay is the timing annotation. 
   // 
   // You must ensure that delay is provided in the loop, where this 
   // non-blocking function is being called. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_fw_export
// 
// Non-blocking forward transport export class. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_fw_export #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_fw_export","class");
   local TARGET m_parent;


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Set the parent and instance name of the blocking transport export. 
   // Sets the maximum and minimum bindings allowed for this export. 
   // The default value of maximum bindings is 1 and minimum binding is 
   // 
   // 0. An error is issued during tlm_bind() if the current binding 
   // exceeds the maximum allowed bindings for the export. An error is 
   // issued during elaboration if the export does not have the minimum 
   // number of specified bindings. 
   //------------------------------------------------------------------------------
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds ,((parent != null) && $cast(_obj, parent)) ? _obj.get_log() : null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_nb_transport_fw_export constructor");
      this.m_parent = parent;
      this.is_nb = 1;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: nb_transport_fw
   // 
   // Non-blocking transport function of the transport export. This function 
   // is internally called by the bound transport port. This function calls the 
   // ~nb_transport_fw()~ method of the parent transactor in which it is 
   // instantiated. If the export is bound to multiple ports then the peer can 
   // be distinguished using the id field passed to the 
   // nb_transport_fw() method. 
   // 
   // The trans argument is a handle of the transaction object, phis the 
   // handle of phase class to specify the phase of a transaction trans, 
   // and the delay argument is the timing annotation. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_port
// 
// Bidirectional non-blocking port. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_port #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_port","class");
   local INITIATOR m_parent;
   
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name , ((parent != null) && $cast(_obj,parent)) ?_obj.get_log() : null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_nb_transport_port constructor");
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_export
// 
// Bidirectional non-blocking export. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_export #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data, type PHASE = vmm_tlm::phase_e ) extends vmm_tlm_export_base#(DATA, PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_export","class");
   local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds ,((parent != null) && $cast(_obj, parent)) ? _obj.get_log() : null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_nb_transport_export constructor");
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_bw_port
// 
// Non-blocking transport port for the backward path. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_bw_port #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data, type PHASE = vmm_tlm::phase_e) extends vmm_tlm_port_base#(DATA,PHASE);
                                            
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_bw_port","class");

   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent and instance name of the non-blocking backward 
   // transport port. 
   //------------------------------------------------------------------------------
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj, parent)) ? _obj: null , name, ((parent != null ) && $cast(_obj,parent))? _obj.get_log() : null );
      this.is_nb = 1;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: nb_transport_bw
   // 
   // Non-blocking transport function of the port. Calls the 
   // ~nb_transport_bw()~ method of the bound export. The argument 
   // trans is a handle of the transaction object, ph is a handle of the 
   // phase class, and delay is the timing annotation. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_nb_transport_bw_export
// 
// Non-blocking backward transport export class. 
//------------------------------------------------------------------------------
class vmm_tlm_nb_transport_bw_export #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data , type PHASE = vmm_tlm::phase_e) extends vmm_tlm_export_base#(DATA,PHASE);
                                           
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_nb_transport_bw_export","class");
   local TARGET m_parent;


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent and instance name of the blocking transport export. 
   // Sets the maximum and minimum bindings allowed for this export. 
   // The default value of maximum bindings is 1 and minimum bindings 
   // is 0. An error is generated during ~tlm_bind()~, if the current binding 
   // exceeds the maximum allowed bindings for the export. An error is 
   // generated during elaboration, if the export does not contain the 
   // minimum number of specified bindings. 
   //------------------------------------------------------------------------------
   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj, parent)) ? _obj: null , name, max_binds, min_binds,((parent != null) && $cast(_obj,parent))? _obj.get_log(): null  );
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_nb_transport_bw_export constructor");
      this.m_parent = parent;
      this.is_nb = 1;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: nb_transport_bw
   // 
   // Non-blocking transport function of the transport export. This function 
   // is internally called by the bound transport port. This function calls the 
   // ~nb_transport_bw()~ method of parent transactor it is instantiated 
   // in.The argument id specifies the binding id of this export. If the 
   // export is bound to multiple ports then the peer can be distinguished 
   // using the id passed to the ~nb_transport_bw()~.The trans 
   // argument is a handle of the transaction object, ph is the handle of 
   // phase class to specify the phase of a transaction trans, the delay 
   // argument is the timing annotation. 
   //------------------------------------------------------------------------------
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

   function void get_peers(output vmm_tlm_analysis_export_base#(DATA) peers[$]);
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

   /* local */ function void  bind_peer(vmm_tlm_analysis_export_base#(DATA) peer);
      this.bindings.push_back(peer);
      this.m_bindings++;
	  return;
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

   function void get_peers(output vmm_tlm_analysis_port_base#(DATA) peers[$]);
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

   function void set_max_bindings(int unsigned max);
      this.m_max_binds = max;
   endfunction : set_max_bindings

   function void set_min_bindings(int unsigned min);
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_analysis_port
// 
// Analysis ports are useful to broadcast transactions, to observers like 
// scoreboards and functional coverage models. Analysis ports can be 
// bound to any number of observers, through the observers analysis 
// export. 
// 
// The analysis port calls the write method of all the observers bound 
// to it. 
//------------------------------------------------------------------------------
class vmm_tlm_analysis_port #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data) extends vmm_tlm_analysis_port_base#(DATA);
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_analysis_export
// 
// Analysis exports are used by observer components that implement 
// a write method to receive broadcast transactions from other 
// components that instantiate the <vmm_tlm_analysis_port> class. 
// Analysis exports can be bound to any number of analysis ports, as 
// specified in the constructor of the analysis export. The different 
// analysis ports connected to this export can be distinguished using 
// the peer identity of the analysis port. 
// 
// The analysis export implements the write method, which is called by 
// the analysis ports that are bound to this export. 
//------------------------------------------------------------------------------
class vmm_tlm_analysis_export #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), type DATA = vmm_data) extends vmm_tlm_analysis_export_base#(DATA);
   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_analysis_export","class");
   local TARGET m_parent;

   function  new(TARGET parent, string name , int max_binds = 1 , int min_binds = 0);
      super.new( ($cast(_obj, parent)) ? _obj : null, name, max_binds, min_binds,((parent != null) && $cast(_obj,parent))? _obj.get_log():null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_analysis_export constructor");
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
	  return(vmm_tlm::ILLEGAL_TYPE);
   endfunction
    
   virtual function vmm_tlm::sync_e nb_transport_bw(DATA trans, ref PHASE ph, ref int delay);
      `vmm_error(log, "Virtual base class function nb_transport_bw is not extended");
	  return(vmm_tlm::ILLEGAL_TYPE);
   endfunction 

   virtual task b_transport(DATA trans , ref int delay);
      `vmm_error(log, "Virtual base class task b_transport is not extended");
   endtask : b_transport
   
endclass: vmm_tlm_socket_base

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_initiator_socket
// 
// Bidirectional socket port providing both blocking and non-blocking 
// paths. 
//------------------------------------------------------------------------------
class vmm_tlm_initiator_socket #(type INITIATOR = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), 
                                 type DATA = vmm_data, 
                                 type PHASE = vmm_tlm::phase_e) 
                                   extends vmm_tlm_socket_base#(DATA,PHASE);

   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_initiator_socket","class");
   /* local */ local INITIATOR m_parent;
   
   function new(INITIATOR parent, string name);
      super.new(($cast(_obj,parent))? _obj: null , name , ((parent != null) && $cast(_obj,parent))? _obj.get_log(): null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_initiator_socket constructor");
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_target_socket
// 
// Bidirectional socket export providing both blocking and non-blocking 
// paths. 
//------------------------------------------------------------------------------
class vmm_tlm_target_socket #(type TARGET = vmm_tlm_xactor#(vmm_data, vmm_tlm::phase_e), 
                              type DATA = vmm_data, 
                              type PHASE = vmm_tlm::phase_e) 
                                extends vmm_tlm_socket_base#(DATA,PHASE);

   /* local */ static local vmm_object _obj;
   //vmm_log log = new("vmm_tlm_target_socket","class");
   /* local */ local TARGET m_parent;

   function new(TARGET parent, string name, int max_binds = 1, int min_binds = 0);
      super.new(($cast(_obj,parent))? _obj:null , name,((parent != null ) && $cast(_obj,parent))? _obj.get_log(): null);
      if(parent == null) 
         `vmm_error(log,"Null parent reference passed to vmm_tlm_target_socket constructor");
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_reactive_if
// 
// TLM Reactive class providing an API similar to the vmm_channel's 
// active slot. 
//------------------------------------------------------------------------------
class vmm_tlm_reactive_if #(type DATA = vmm_data, int q_size = 1) extends vmm_object;
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
   

   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent, if it is an extension <vmm_object>. Sets the name of 
   // the instance. 
   //------------------------------------------------------------------------------
   function new(vmm_object parent, string name);
      super.new(parent,name);
      m_nb_id = 100000;
      m_b_pending = 0;
      m_in_process = 0;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_bind
   // 
   // Binds the TLM port passed as an argument to the corresponding 
   // TLM export depending on the enum passed in second argument. 
   //------------------------------------------------------------------------------
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
   

   //------------------------------------------------------------------------------
   // FUNCTION: try_get
   // 
   // Returns null if no transaction object is received. If there are more 
   // than one object then returns the first transaction object. Subsequent 
   // try_get calls must be preceded by calling the ~completed()~ 
   // method. Else, an error is issued. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // TASK: get
   // 
   // Blocks until a transaction object is available. If there is more than one 
   // object then gets the first transaction object. Subsequent get calls 
   // must be preceded by calling the ~completed()~ method. Else, an 
   // error is issued. 
   //------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: completed
   // 
   // The completed method must be called by the transactor to indicate 
   // the completion of active transaction. The blocking port which initiated 
   // the transaction will be unblocked and nb_transport_bw method is 
   // called for non-blocking bi-directional with TLM_COMPLETED phase. 
   // 
   // For <vmm_data> derivatives vmm_data::ENDED is also indicated. 
   // The transaction is removed from the pending queue only when 
   // completed is called. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_transport_interconnect_base
// 
// Interconnect transport base class. 
// 
// Base class for vmm_tlm_transport_interconnect class. This 
// class contains tlm_bind method which is used to connect below 
// ports and exports. 
// 
// - <vmm_tlm_b_transport_port> to <vmm_tlm_nb_transport_export> 
// - <vmm_tlm_b_transport_port> to <vmm_tlm_nb_transport_fw_export> 
// - <vmm_tlm_nb_transport_port> to <vmm_tlm_b_transport_export>
// - <vmm_tlm_nb_transport_fw_port> to <vmm_tlm_b_transport_export> 
// 
// Any user-defined interconnect class should be extended from this 
// base class. The parameter DATA is the type of the transaction object 
// of the port/export services. The default type is <vmm_data>. The 
// parameter PHASE is the type of the phasing class. The default value 
// is vmm_tlm::phase_e. 
//------------------------------------------------------------------------------
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


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent, if it is an extension of <vmm_object>. Sets the name 
   // of the instance. 
   //------------------------------------------------------------------------------
   function new(vmm_object parent, string name);
      super.new(parent,name);
      is_bound = 0;
      is_fw = 0;
   endfunction: new


   //------------------------------------------------------------------------------
   // FUNCTION: tlm_bind
   // 
   // Binds the TLM port to TLM export. 
   //------------------------------------------------------------------------------
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

//------------------------------------------------------------------------------
// CLASS: vmm_tlm_transport_interconnect
// 
// Interconnect transport class. 
// 
// Class extended from <vmm_tlm_transport_interconnect_base>. 
//
// This class is specific to vmm_tlm::phase_e type. 
// 
// The parameter DATA is the type of the transaction object of the port/ 
// export services. The default type is <vmm_data>. 
//------------------------------------------------------------------------------
class vmm_tlm_transport_interconnect #(type DATA = vmm_data) extends vmm_tlm_transport_interconnect_base#(DATA);


   //------------------------------------------------------------------------------
   // FUNCTION: new
   // 
   // Sets the parent, if it is an extension of <vmm_object>. Sets the name 
   // of the instance. 
   //------------------------------------------------------------------------------
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
   integer _tmp_last_idx;

   begin
      forever 
      begin
         @b_start_event;
         fork
            begin
               vmm_tlm::phase_e cur_ph = vmm_tlm::BEGIN_REQ;
               vmm_tlm::sync_e m_sync_e;
`ifdef VCS
               DATA cur_data = pending_data[$];
               int cur_delay = m_delay[$];
			`else //Simplifying the code to ensure non-VCS simulators can compile it
			   DATA cur_data;
			   int cur_delay;
			   
			   _tmp_last_idx = pending_data.size() - 1;
			   cur_data = pending_data[_tmp_last_idx];

			   _tmp_last_idx = m_delay.size() - 1;
               cur_delay = m_delay[_tmp_last_idx];
			`endif   
               if(is_fw == 1)
               begin
                  m_sync_e = nb_fw_port.nb_transport_fw(cur_data, cur_ph, cur_delay);
			      
`ifdef VCS
                  m_delay[$] = cur_delay;
				  `else //Simplifying the code to ensure non-VCS simulators can compile it
				  _tmp_last_idx = m_delay.size() - 1;
				  m_delay[_tmp_last_idx] = cur_delay;
				  `endif
                  
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
						  
`ifdef VCS
                          m_delay[$] = cur_delay;
						  `else //Simplifying the code to ensure non-VCS simulators can compile it 
				  		  _tmp_last_idx = m_delay.size() - 1;
				  		  m_delay[_tmp_last_idx] = cur_delay;
						  `endif
                          
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
      integer _tmp_last_idx;
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
		  
`ifdef VCS
           m_delay[$] = delay;
		  `else //Simplifying the code to ensure non-VCS simulators can compile it 
		   _tmp_last_idx = m_delay.size() - 1;
		   m_delay[_tmp_last_idx] = delay;
		  `endif
		  
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
      integer _tmp_last_idx;
   begin
      forever
      begin
         @nb_start_event;
         fork
         begin
            int data_que[$], ph_que[$];
            DATA t_data;

`ifdef VCS
            DATA cur_data = pending_data[$];
            int delay = m_delay[$];
            vmm_tlm::phase_e cur_ph = m_ph[$];
		    
			`else //Simplifying the code to ensure non-VCS simulators can compile it 
		    DATA cur_data;
			int delay ;
			vmm_tlm::phase_e cur_ph;
			
			_tmp_last_idx = pending_data.size() - 1;
		    cur_data = pending_data[_tmp_last_idx]; 

			_tmp_last_idx = m_delay.size() - 1;
            delay = m_delay[_tmp_last_idx];

			_tmp_last_idx = m_ph.size() - 1;
            cur_ph = m_ph[_tmp_last_idx];
		    `endif

            
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
