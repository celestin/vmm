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


typedef class vmm_mam_region;
typedef class vmm_mam;



//------------------------------------------------------------------------------
// CLASS: vmm_ral_vreg_callbacks
// Base class for virtual register descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_vreg_callbacks extends vmm_ral_callbacks;
   string fname = "";
   int    lineno = 0;


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This callback method is invoked before a value is written to a virtual register in the
   // DUT. The written value, if modified, changes the actual value that is written. The path
   // and domain used to write to the register can also be modified. This callback method is
   // only invoked when the <vmm_ral_vreg::write()> method is used to write to the register
   // inside the DUT. This callback method is not invoked when the memory location implementing
   // a virtual register, is written to using the <vmm_ral_mem::write()> method. Because
   // writing a register causes all of the fields it contains to be written, all registered
   // <vmm_ral_vfield_callbacks::pre_write()> methods with the fields contained in
   // the register will also be invoked before all registered register callback methods.
   // Because the memory implementing the virtual field is accessed through its own abstraction
   // class, all of its registered <vmm_ral_mem_callbacks::pre_write()> methods will
   // also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task pre_write(vmm_ral_vreg                      rg,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write


   //------------------------------------------------------------------------------
   // TASK: post_write
   // This callback method is invoked after a value is successfully written to a register
   // in the DUT. If a physical write access did not return vmm_rw::IS_OK, this method is not
   // called. This callback method is only invoked when the <vmm_ral_vreg::write()> method
   // is used to write to the register inside the DUT. This callback method is not invoked when
   // the memory location implementing a virtual register, is written to using the <vmm_ral_mem::write()>
   // method. Because writing a register causes all of the fields it contains to be written,
   // all registered <vmm_ral_vfield_callbacks::post_write()> methods with the fields
   // contained in the register will also be invoked before all registered register callback
   // methods. Because the memory implementing the virtual field is accessed through its
   // own abstraction class, all of its registered <vmm_ral_mem_callbacks::post_write()>
   // methods will also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task post_write(vmm_ral_vreg                  rg,
                           longint unsigned              idx,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write


   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This callback method is invoked before a value is read from a register in the DUT. The
   // path and domain used to read the register can be modified. This callback method is only
   // invoked when the <vmm_ral_vreg::read()> method is used to read to the register inside
   // the DUT. This callback method is not invoked when the memory location implementing
   // a virtual register, is read to using the <vmm_ral_mem::read()> method. Because reading
   // a register causes all of the fields it contains to be written, all registered <vmm_ral_vfield_callbacks::pre_read()>
   // methods with the fields contained in the register will also be invoked before all registered
   // register callback methods. Because the memory implementing the virtual field is accessed
   // through its own abstraction class, all of its registered <vmm_ral_mem_callbacks::pre_read()>
   // methods will also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task pre_read(vmm_ral_vreg         rg,
                         longint unsigned     idx,
                         ref vmm_ral::path_e  path,
                         ref string           domain);
   endtask: pre_read


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This callback method is invoked after a value is successfully read from a register in
   // the DUT. The rdat and status values are the values that will be ultimately returned by
   // the <vmm_ral_vreg::read()> method and can be modified. If a physical read access did
   // not return vmm_rw::IS_OK, this method is not called. This callback method is only invoked
   // when the <vmm_ral_vreg::read()> method is used to read to the register inside the DUT.
   // This callback method is not invoked when the memory location implementing a virtual
   // register, is read to using the <vmm_ral_mem::read()> method. Because reading a register
   // causes all of the fields it contains to be written, all registered <vmm_ral_vfield_callbacks::post_read()>
   // methods with the fields contained in the register will also be invoked before all registered
   // register callback methods. Because the memory 
   //------------------------------------------------------------------------------
   virtual task post_read(vmm_ral_vreg                      rg,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          input vmm_ral::path_e             path,
                          input string                      domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_vreg_callbacks



//------------------------------------------------------------------------------
// CLASS: vmm_ral_vreg
// Base class for virtual register descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_vreg 
`ifdef VMM_RAL_BASE
extends `VMM_RAL_BASE
`endif // VMM_RAL_BASE
;
   static vmm_log log = new("RAL", "virtual register");

   local bit locked;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   local vmm_ral_block parent;
`endif
   local string name;
   local int unsigned  n_bits;
   local int unsigned  n_used_bits;

   local vmm_ral_vfield fields[$];   // Fields in LSB to MSB order

   local vmm_ral_vreg_callbacks callbacks[$];

   local vmm_ral_mem                   mem;     // Where is it implemented?
   local bit [`VMM_RAL_ADDR_WIDTH-1:0] offset;  // Start of vreg[0]
   local int unsigned                  incr;    // From start to start of next
   local longint unsigned              size;    //number of vregs
   local bit                           is_static;

   local vmm_mam_region   region;    // Not NULL if implemented via MAM
  
   local semaphore atomic;   // Field RMW operations must be atomic
   local string fname = "";
   local int lineno = 0;
   local bit read_in_progress;
   local bit write_in_progress;

   extern /*local*/ function new(vmm_ral_block                 parent,
                                 string                        name,
                                 int unsigned                  n_bits,
                                 bit [`VMM_RAL_ADDR_WIDTH-1:0] offset = 0,
                                 vmm_ral_mem                   mem    = null,
                                 longint unsigned              size   = 0,
                                 int unsigned                  incr   = 0);

   /*local*/ extern function void Xlock_modelX();
   
   /*local*/ extern function void register_field(vmm_ral_vfield field);
   /*local*/ extern task XatomicX(bit on);
   
   extern function void reset(vmm_ral::reset_e kind = vmm_ral::HARD);


   //------------------------------------------------------------------------------
   // FUNCTION: get_name
   // Returns the name of the register corresponding to the instance of the descriptor. 
   //------------------------------------------------------------------------------
   extern virtual function string get_name();

   //------------------------------------------------------------------------------
   // FUNCTION: get_fullname
   // Returns the hierarchical name of the register corresponding to the instance of the
   // descriptor. The name of the top-level block or system is not included in the fully-qualified
   // name as it is implicit for every RAL model. 
   //------------------------------------------------------------------------------
   extern virtual function string get_fullname();

   //------------------------------------------------------------------------------
   // FUNCTION: get_block
   // Returns a reference to the descriptor of the block that includes the register corresponding
   // to the descriptor instance. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_block get_block();


   //------------------------------------------------------------------------------
   // FUNCTION: implement
   // Dynamically implement, resize or relocate a set of virtual registers of the specified
   // size, in the specified memory and offset. If an offset increment is specified, each
   // virtual register is implemented at the specified offset from the previous one. If an
   // offset increment of 0 is specified, virtual registers are packed as closely as possible
   // in the memory. If no memory is specified, the virtual register set is in the same memory,
   // at the same offset using the same offset increment as originally implemented. The initial
   // value of the newly-implemented or relocated set of virtual registers is whatever values
   // are currently stored in the memory now implementing them. Returns TRUE if the memory
   // can implement the number of virtual registers at the specified offset and increment.
   // Returns FALSE if the memory cannot implement the specified virtual register set. The
   // memory region used to implement a set of virtual registers is reserved to prevent it
   // from being allocated for another purpose by the memory's default memory allocation
   // manager. 
   //------------------------------------------------------------------------------
   extern virtual function bit implement(longint unsigned              n,
                                         vmm_ral_mem                   mem    = null,
                                         bit [`VMM_RAL_ADDR_WIDTH-1:0] offset = 0,
                                         int unsigned                  incr   = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: allocate
   // Dynamically implement, resize or relocate a set of virtual registers of the specified
   // size to a randomly allocated region of the appropriate size in the address space managed
   // by the specified memory allocation manager. The initial value of the newly-implemented
   // or relocated set of virtual registers is whatever values are currently stored in the
   // memory region now implementing them. Returns a reference to a memory region descriptor
   // if the memory allocation manager was able to allocate a region that can implement the
   // number of virtual registers. Returns null if the memory allocation manager cannot
   // allocate a suitable region. Statically-implemented virtual registers cannot be
   // implemented, resized nor relocated. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_mam_region allocate(longint unsigned n,
                                                   vmm_mam          mam);

   //------------------------------------------------------------------------------
   // FUNCTION: get_region
   // Returns a reference to a memory region descriptor that implements the set of virtual
   // registers. Returns null if the virtual registers are not currently implemented. A
   // region implementing a set of virtual registers must not be released using the vmm_mam::release_region()
   // method. It must be released using the <vmm_ral_vreg::release_region()> method.
   // 
   //------------------------------------------------------------------------------
   extern virtual function vmm_mam_region get_region();

   //------------------------------------------------------------------------------
   // FUNCTION: release_region
   // Release the memory region used to implement the set of virtual registers and return
   // it to the pool of available memory that can be allocated by the memory's default allocation
   // manager. The virtual registers are subsequently considered as unimplemented and
   // can no longer be accessed. Statically-implemented virtual registers cannot be released.
   // 
   //------------------------------------------------------------------------------
   extern virtual function void release_region();


   //------------------------------------------------------------------------------
   // FUNCTION: get_memory
   // Returns a reference to the memory abstraction class for the memory that implements
   // the set of virtual registers corresponding to the descriptor instance. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_mem get_memory();

   //------------------------------------------------------------------------------
   // FUNCTION: get_n_domains
   // Returns the number of domains that share the memory implementing this set of virtual
   // registers. The name of the domains can be obtained with the <vmm_ral_reg::get_domains()>
   // method. 
   //------------------------------------------------------------------------------
   extern virtual function int get_n_domains();

   //------------------------------------------------------------------------------
   // FUNCTION: get_domains
   // Fills the specified dynamic array with the names of all the block-level domains that
   // can access the memory implementing this set of virtual registers. The order of the domain
   // names is not specified. 
   //------------------------------------------------------------------------------
   extern virtual function void get_domains(ref string domains[]);

   //------------------------------------------------------------------------------
   // FUNCTION: get_access
   // Returns the specification of the behavior of the memory used to implement the set of
   // virtual register when written and read. If the memory is shared across more than one
   // domain, a domain name must be specified. If access restrictions are present when accessing
   // a memory through the specified domain, the access mode returned takes the access restrictions
   // into account. For example, a read-write memory accessed through a domain with read-only
   // restrictions would return vmm_ral::RO. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral::access_e get_access(string domain = "");

   //------------------------------------------------------------------------------
   // FUNCTION: get_rights
   // Returns the access rights of the memory implementing this set of virtual registers.
   // Returns vmm_ral::RW, vmm_ral::RO or vmm_ral::WO. See <vmm_ral_mem::get_rights()>
   // for more details. If the memory implementing this set of virtual registers is shared
   // in more than one domain, a domain name must be specified. If the memory is not shared in
   // the specified domain, an error message is issued and vmm_ral::RW is returned. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral::access_e get_rights(string domain = "");
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_offset_in_memory(longint unsigned idx);

   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_address_in_system(longint unsigned idx,
                                                                               string domain = "");


   //------------------------------------------------------------------------------
   // FUNCTION: get_size
   // Returns the number of virtual registers in the virtual register array. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_size();

   //------------------------------------------------------------------------------
   // FUNCTION: get_n_bytes
   // Returns the width, in number of bytes, of the virtual register. The width of a virtual
   // register is always a multiple of the width of the memory locations used to implement
   // it. For example, a virtual register containing two 1-byte fields implemented in a memory
   // with 4-bytes memory locations is 4-byte wide. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_n_bytes();

   //------------------------------------------------------------------------------
   // FUNCTION: get_n_memlocs
   // Returns the number of memory locations used by a single virtual register. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_n_memlocs();

   //------------------------------------------------------------------------------
   // FUNCTION: get_incr
   // Returns the number of memory locations between two individual virtual registers in
   // the same array. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_incr();


   //------------------------------------------------------------------------------
   // FUNCTION: display
   // Displays the image created by the <vmm_ral_vreg::psdisplay()> method to the standard
   // output. 
   //------------------------------------------------------------------------------
   extern virtual function void display(string prefix = "");
   extern virtual function void display_domain(string prefix = "",
                                               string domain = "");

   //------------------------------------------------------------------------------
   // FUNCTION: psdisplay
   // Creates a human-readable description of the register and the fields it contains. Each
   // line of the description is prefixed with the specified prefix. 
   //------------------------------------------------------------------------------
   extern virtual function string psdisplay(string prefix = "");

   //------------------------------------------------------------------------------
   // FUNCTION: psdisplay_domain
   // Creates a human-readable description of the register and the fields it contains. Each
   // line of the description is prefixed with the specified prefix. If a domain is specified,
   // the address of the register within that domain is used. 
   //------------------------------------------------------------------------------
   extern virtual function string psdisplay_domain(string prefix = "",
                                                   string domain = "");


   //------------------------------------------------------------------------------
   // FUNCTION: get_fields
   // Fills the specified dynamic array with the descriptor for all of the virtual fields
   // contained in the virtual register. Fields are ordered from least-significant position
   // to most-significant position within the register. 
   //------------------------------------------------------------------------------
   extern virtual function void get_fields(ref vmm_ral_vfield fields[]);

   //------------------------------------------------------------------------------
   // FUNCTION: get_field_by_name
   // Finds a virtual field with the specified name in the register and returns its descriptor.
   // If no fields are found, returns null. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_vfield get_field_by_name(string name);


   //------------------------------------------------------------------------------
   // TASK: write
   // Writes the specified value in the specified virtual register in the design using the
   // specified access path. If the memory implementing the virtual register is shared by
   // more than one physical interface, a domain must be specified if a physical access is
   // used (front-door access). The optional value of the arguments: data_id scenario_id
   // stream_id ...are passed to the back-door access method or used to set the corresponding
   // vmm_data class properties in the <vmm_rw_access> transaction descriptors that are
   // necessary to execute this write operation. This allows the physical and back-door
   // write accesses to be traced back to the higher-level transaction that caused the access
   // to occur. 
   //------------------------------------------------------------------------------
   extern virtual task write(input  longint unsigned             idx,
                             output vmm_rw::status_e             status,
                             input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                             input  string                       domain = "",
                             input  int                          data_id = -1,
                             input  int                          scenario_id = -1,
                             input  int                          stream_id = -1,
                             input  string                       fname = "",
                             input  int                          lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: read
   // Reads the current value of the specified virtual register from the design using the
   // specified access path. If the memory implementing the virtual register is shared by
   // more than one physical interface, a domain must be specified if a physical access is
   // used (front-door access). The optional value of the arguments: data_id scenario_id
   // stream_id ...are passed to the back-door access method or used to set the corresponding
   // vmm_data class properties in the <vmm_rw_access> transaction descriptors that are
   // necessary to execute this read operation. This allows the physical and back-door read
   // accesses to be traced back to the higher-level transaction that caused the access to
   // occur. 
   //------------------------------------------------------------------------------
   extern virtual task read(input  longint unsigned             idx,
                            output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                            input  string                       domain = "",
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: poke
   // Deposit the specified value in the specified virtual register in the design, as-is,
   // using a back-door access. The memory implementing the virtual register must provide
   // a back-door access. The optional value of the arguments: data_id scenario_id stream_id
   // ...are passed to the back-door access method. This allows the physical and back-door
   // write accesses to be traced back to the higher-level transaction that caused the access
   // to occur. 
   //------------------------------------------------------------------------------
   extern virtual task poke(input  longint unsigned             idx,
                            output vmm_rw::status_e             status,
                            input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: peek
   // Reads the current value of the specified virtual register from the design using a back-door
   // access. The memory implementing the virtual register must provide a back-door access.
   // The optional value of the arguments: data_id scenario_id stream_id ...are passed
   // to the back-door access method. This allows the physical and back-door read accesses
   // to be traced back to the higher-level transaction that caused the access to occur. 
   //------------------------------------------------------------------------------
   extern virtual task peek(input  longint unsigned             idx,
                            output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);
  

   //------------------------------------------------------------------------------
   // FUNCTION: prepend_callback
   // Prepends the specified callback extension instance to the registered callbacks for
   // this register descriptor. Callbacks are invoked in the reverse order of registration.
   // Note that the corresponding <vmm_ral_vfield> callback methods will be invoked before
   // the virtual register callback methods. 
   //------------------------------------------------------------------------------
   extern function void prepend_callback(vmm_ral_vreg_callbacks cb,
                                         string         fname = "",
                                         int            lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: append_callback
   // Appends the specified callback extension instance to the registered callbacks for
   // this virtual register descriptor. Callbacks are invoked in the order of registration.
   // Note that the corresponding <vmm_ral_vfield> callback methods will be invoked before
   // the virtual register callback methods. 
   //------------------------------------------------------------------------------
   extern function void append_callback(vmm_ral_vreg_callbacks cb,
                                         string         fname = "",
                                         int            lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: unregister_callback
   // Removes the specified callback extension instance from the registered callbacks
   // for this register descriptor. A warning message is issued if the callback instance
   // has not been previously registered. 
   //------------------------------------------------------------------------------
   extern function void unregister_callback(vmm_ral_vreg_callbacks cb);
endclass: vmm_ral_vreg


function vmm_ral_vreg::new(vmm_ral_block                 parent,
                           string                        name,
                           int unsigned                  n_bits,
                           bit [`VMM_RAL_ADDR_WIDTH-1:0] offset = 0,
                           vmm_ral_mem                   mem = null,
                           longint unsigned              size = 0,
                           int unsigned                  incr = 0);
   `ifdef VMM_12_UNDERPIN_VMM_RAL
     super.new(parent, name);
     this.set_object_name(name, "RAL");
   `else 
     this.parent = parent;
   `endif
   this.locked    = 0;

`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.register_vreg(this);
`else
   begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      parent.register_vreg(this); 
   end
`endif
   this.name = name;

   if (n_bits == 0) begin
      `vmm_error(this.log, $psprintf("Virtual register \"%s\" cannot have 0 bits", this.get_fullname()));
      n_bits = 1;
   end
   if (n_bits > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Virtual register \"%s\" cannot have more than %0d bits (%0d)", this.get_fullname(), `VMM_RAL_DATA_WIDTH, n_bits));
      n_bits = `VMM_RAL_DATA_WIDTH;
   end
   this.n_bits = n_bits;
   this.n_used_bits = 0;

   if (mem != null) begin
      void'(this.implement(size, mem, offset, incr));
      this.is_static = 1;
   end
   else begin
      this.mem = null;
      this.is_static = 0;
   end

   this.atomic = new(1);
endfunction: new


function void vmm_ral_vreg::Xlock_modelX();
   if (this.locked) return;

   this.locked = 1;
endfunction: Xlock_modelX


function void vmm_ral_vreg::register_field(vmm_ral_vfield field);
   int offset;
   int idx;
   
   if (this.locked) begin
      `vmm_error(this.log, "Cannot add virtual field to locked virtual register model");
      return;
   end

   if (field == null) `vmm_fatal(this.log, "Attempting to register NULL virtual field");

   // Store fields in LSB to MSB order
   offset = field.get_lsb_pos_in_register();

   idx = -1;
   foreach (this.fields[i]) begin
      if (offset < this.fields[i].get_lsb_pos_in_register()) begin
         int j = i;
         this.fields.insert(j, field);
         idx = i;
         break;
      end
   end
   if (idx < 0) begin
      this.fields.push_back(field);
      idx = this.fields.size()-1;
   end

   this.n_used_bits += field.get_n_bits();
   
   // Check if there are too many fields in the register
   if (this.n_used_bits > this.n_bits) begin
      `vmm_error(this.log, $psprintf("Virtual fields use more bits (%0d) than available in virtual register \"%s\" (%0d)",
                                     this.n_used_bits, this.get_fullname(), this.n_bits));
   end

   // Check if there are overlapping fields
   if (idx > 0) begin
      if (this.fields[idx-1].get_lsb_pos_in_register() +
          this.fields[idx-1].get_n_bits() > offset) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in virtual register \"%s\"",
                                        this.fields[idx-1].get_name(),
                                        field.get_name(),
                                        this.get_fullname()));
      end
   end
   if (idx < this.fields.size()-1) begin
      if (offset + field.get_n_bits() >
          this.fields[idx+1].get_lsb_pos_in_register()) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in virtual register \"%s\"",
                                        field.get_name(),
                                        this.fields[idx+1].get_name(),

                                        this.get_fullname()));
      end
   end
endfunction: register_field


task vmm_ral_vreg::XatomicX(bit on);
   if (on) this.atomic.get(1);
   else begin
      // Maybe a key was put back in by a spurious call to reset()
      void'(this.atomic.try_get(1));
      this.atomic.put(1);
   end
endtask: XatomicX


function void vmm_ral_vreg::reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   // Put back a key in the semaphore if it is checked out
   // in case a thread was killed during an operation
   void'(this.atomic.try_get(1));
   this.atomic.put(1);
endfunction: reset


function string vmm_ral_vreg::get_name();
   return this.name;
endfunction: get_name


function string vmm_ral_vreg::get_fullname();
   vmm_ral_block blk;

   get_fullname = this.get_name();

   // Do not include top-level name in full name
   blk = this.get_block();
   if (blk == null) return get_fullname;
   if (blk.get_parent() == null) return get_fullname;


`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_fullname = {this.parent.get_fullname(), ".", get_fullname};
`else
   begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      get_fullname = {parent.get_fullname(), ".", get_fullname};
   end
`endif
endfunction: get_fullname


function vmm_ral_block vmm_ral_vreg::get_block();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_block = this.parent;
`else
   begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      get_block = parent;
   end
`endif
endfunction: get_block


function bit vmm_ral_vreg::implement(longint unsigned              n,
                                     vmm_ral_mem                   mem = null,
                                     bit [`VMM_RAL_ADDR_WIDTH-1:0] offset = 0,
                                     int unsigned                  incr = 0);

   vmm_mam_region mam_region;

   if(n < 1)
   begin
     `vmm_error(this.log, $psprintf("Attempting to implement virtual register \"%s\" with a subscript less than one doesn't make sense",this.get_fullname()));
      return 0;
   end

   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Attempting to implement virtual register \"%s\" using a NULL vmm_ral_mem reference", this.get_fullname()));
      return 0;
   end

   if (this.is_static) begin
      `vmm_error(this.log, $psprintf("Virtual register \"%s\" is static and cannot be dynamically implemented", this.get_fullname()));
      return 0;
   end

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (mem.get_block() != this.parent) begin
`else
   if (mem.get_block() != this._parent) begin
`endif
      `vmm_error(this.log, $psprintf("Attempting to implement virtual register \"%s\" on memory \"%s\" in a different block",
                                     this.get_fullname(),
                                     mem.get_fullname()));
      return 0;
   end

   begin
      int min_incr = (this.get_n_bytes()-1) / mem.get_n_bytes() + 1;
      if (incr == 0) incr = min_incr;
      if (min_incr > incr) begin
         `vmm_error(this.log, $psprintf("Virtual register \"%s\" increment is too small (%0d): Each virtual register requires at least %0d locations in memory \"%s\".",
                                        this.get_fullname(), incr,
                                        min_incr, mem.get_fullname()));
         return 0;
      end
   end

   // Is the memory big enough for ya?
   if (offset + (n * incr) > mem.get_size()) begin
      `vmm_error(this.log, $psprintf("Given Offset for Virtual register \"%s[%0d]\" is too big for memory %s@'h%0h", this.get_fullname(), n, mem.get_fullname(), offset));
      return 0;
   end

   mam_region = mem.mam.reserve_region(offset,n*incr*mem.get_n_bytes());

   if (mam_region == null) begin
      `vmm_error(this.log, $psprintf("Could not allocate a memory region for virtual register \"%s\"", this.get_fullname()));
      return 0;
   end

   if (this.mem != null) begin
      `vmm_trace(this.log, $psprintf("Virtual register \"%s\" is being moved re-implemented from %s@'h%0h to %s@'h%0h",
                                     this.get_fullname(),
                                     this.mem.get_fullname(),
                                     this.offset,
                                     mem.get_fullname(), offset));
      this.release_region();
   end

   this.region = mam_region;
   this.mem    = mem;
   this.size   = n;
   this.offset = offset;
   this.incr   = incr;
   this.mem.XvregsX.push_back(this);

   return 1;
endfunction: implement


function vmm_mam_region vmm_ral_vreg::allocate(longint unsigned n,
                                               vmm_mam          mam);

   vmm_ral_mem mem;

   if(n < 1)
   begin
     `vmm_error(this.log, $psprintf("Attempting to implement virtual register \"%s\" with a subscript less than one doesn't make sense",this.get_fullname()));
      return null;
   end

   if (mam == null) begin
      `vmm_error(this.log, $psprintf("Attempting to implement virtual register \"%s\" using a NULL vmm_mam reference", this.get_fullname()));
      return null;
   end

   if (this.is_static) begin
      `vmm_error(this.log, $psprintf("Virtual register \"%s\" is static and cannot be dynamically allocated", this.get_fullname()));
      return null;
   end

   mem = mam.get_memory();

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (mem.get_block() != this.parent) begin
`else
   if (mem.get_block() != this._parent) begin
`endif
      `vmm_error(this.log, $psprintf("Attempting to allocate virtual register \"%s\" on memory \"%s\" in a different block",
                                     this.get_fullname(),
                                     mem.get_fullname()));
      return null;
   end

   begin
      int min_incr = (this.get_n_bytes()-1) / mem.get_n_bytes() + 1;
      if (incr == 0) incr = min_incr;
      if (min_incr < incr) begin
         `vmm_error(this.log, $psprintf("Virtual register \"%s\" increment is too small (%0d): Each virtual register requires at least %0d locations in memory \"%s\".",
                                        this.get_fullname(), incr,
                                        min_incr, mem.get_fullname()));
         return null;
      end
   end

   // Need memory at least of size num_vregs*sizeof(vreg) in bytes.
   allocate = mam.request_region(n*incr*mem.get_n_bytes());
   if (allocate == null) begin
      `vmm_error(this.log, $psprintf("Could not allocate a memory region for virtual register \"%s\"", this.get_fullname()));
      return null;
   end

   if (this.mem != null) begin
      `vmm_trace(this.log, $psprintf("Virtual register \"%s\" is being moved re-allocated from %s@'h%0h to %s@'h%0h",
                                     this.get_fullname(),
                                     this.mem.get_fullname(),
                                     this.offset,
                                     mem.get_fullname(),
                                     allocate.get_start_offset()));

      this.release_region();
   end

   this.region = allocate;

   this.mem    = mam.get_memory();
   this.offset = allocate.get_start_offset();
   this.size   = n;
   this.incr   = incr;

   this.mem.XvregsX.push_back(this);
endfunction: allocate


function vmm_mam_region vmm_ral_vreg::get_region();
   return this.region;
endfunction: get_region


function void vmm_ral_vreg::release_region();
   if (this.is_static) begin
      `vmm_error(this.log, $psprintf("Virtual register \"%s\" is static and cannot be dynamically released", this.get_fullname()));
      return;
   end

   if (this.mem != null) begin
      foreach (this.mem.XvregsX[i]) begin
         if (this.mem.XvregsX[i] == this) begin
            this.mem.XvregsX.delete(i);
            break;
         end
      end
   end 
   if (this.region != null) begin
      this.region.release_region();
   end

   this.region = null;
   this.mem    = null;
   this.size   = 0;
   this.offset = 0;

   this.reset();
endfunction: release_region


function vmm_ral_mem vmm_ral_vreg::get_memory();
   return this.mem;
endfunction: get_memory


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_vreg::get_offset_in_memory(longint unsigned idx);
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_offset_in_memory() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return 0;
   end

   return this.offset + idx * this.incr;
endfunction


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_vreg::get_address_in_system(longint unsigned idx,
                                                                           string domain = "");
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot get address of of unimplemented virtual register \"%s\".", this.get_fullname()));
      return 0;
   end

   return this.mem.get_address_in_system(this.get_offset_in_memory(idx),
                                         domain);
endfunction: get_address_in_system


function int unsigned vmm_ral_vreg::get_size();
   if (this.size == 0) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_size() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return 0;
   end

   return this.size;
endfunction: get_size


function int unsigned vmm_ral_vreg::get_n_bytes();
   return ((this.n_bits-1) / 8) + 1;
endfunction: get_n_bytes


function int unsigned vmm_ral_vreg::get_n_memlocs();
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_n_memlocs() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return 0;
   end

   return (this.get_n_bytes()-1) / this.mem.get_n_bytes() + 1;
endfunction: get_n_memlocs


function int unsigned vmm_ral_vreg::get_incr();
   if (this.incr == 0) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_incr() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return 0;
   end

   return this.incr;
endfunction: get_incr


function int vmm_ral_vreg::get_n_domains();
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_n_domains() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return 0;
   end

   get_n_domains = this.mem.get_n_domains();
endfunction: get_n_domains


function void vmm_ral_vreg::get_domains(ref string domains[]);
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_domains() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return;
   end

   this.mem.get_domains(domains);
endfunction: get_domains


function vmm_ral::access_e vmm_ral_vreg::get_access(string domain = "");
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_rights() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return vmm_ral::RW;
   end

   get_access = this.mem.get_access(domain);
endfunction: get_access


function vmm_ral::access_e vmm_ral_vreg::get_rights(string domain = "");
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vreg::get_rights() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      return vmm_ral::RW;
   end

   get_rights = this.mem.get_rights(domain);
endfunction: get_rights


function void vmm_ral_vreg::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function void vmm_ral_vreg::display_domain(string prefix = "",
                                           string domain = "");
   $write("%s\n", this.psdisplay_domain(prefix, domain));
endfunction: display_domain


function string vmm_ral_vreg::psdisplay(string prefix = "");
   return this.psdisplay_domain(prefix);
endfunction: psdisplay

function string vmm_ral_vreg::psdisplay_domain(string prefix = "",
                                               string domain = "");
   string res_str = "";
   string t_str = "";
   bit with_debug_info = 1'b0;
   $sformat(psdisplay_domain, "%sVirtual register %s -- ", prefix,
            this.get_fullname());
   if (this.size == 0) $sformat(psdisplay_domain, "%sunimplemented", psdisplay_domain);
   else begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] addr0;

      addr0 = this.get_address_in_system(0, domain);

      $sformat(psdisplay_domain, "%s[%0d] in %0s['h%0h+'h%0h] @'h%h+'h%h", psdisplay_domain,
               this.size, this.mem.get_fullname(), this.offset, this.incr, 
               addr0, this.get_address_in_system(1, domain) - addr0);
  end
   foreach(this.fields[i]) begin
      $sformat(psdisplay_domain, "%s\n%s", psdisplay_domain,
               this.fields[i].psdisplay({prefix, "   "}));
   end
   foreach ( this.callbacks[i]) begin
      if (this.callbacks[i].fname != "" && this.callbacks[i].lineno != 0) begin
         with_debug_info = 1'b1;
         $sformat(t_str, "callback registered in %s:%0d\n",this.callbacks[i].fname, this.callbacks[i].lineno);
         res_str = {res_str, t_str};
      end
   end
   if (callbacks.size() != 0) begin
      $sformat(t_str, "\nTotal %0d callbacks have been registered for %s",callbacks.size(), this.get_name());
      psdisplay_domain= {psdisplay_domain, t_str };
   end
   if (with_debug_info == 1'b1) begin
      psdisplay_domain= {psdisplay_domain, "\ncallbacks with debug info.."};
      psdisplay_domain= {psdisplay_domain, "\n", res_str };
   end

endfunction: psdisplay_domain


function void vmm_ral_vreg::get_fields(ref vmm_ral_vfield fields[]);
   fields = new [this.fields.size()];
   foreach(this.fields[i]) begin
      fields[i] = this.fields[i];
   end
endfunction: get_fields


function vmm_ral_vfield vmm_ral_vreg::get_field_by_name(string name);
   foreach (this.fields[i]) begin
      if (this.fields[i].get_name() == name) begin
         return this.fields[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate field \"%s\" in virtual register \"%s\".",
                                    name, this.get_fullname()));
   get_field_by_name = null;
endfunction: get_field_by_name


task vmm_ral_vreg::write(input  longint unsigned             idx,
                         output vmm_rw::status_e             status,
                         input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                         input  string                       domain = "",
                         input  int                          data_id = -1,
                         input  int                          scenario_id = -1,
                         input  int                          stream_id = -1,
                         input  string                       fname = "",
                         input  int                          lineno = 0);

   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
   int lsb;

   this.write_in_progress = 1'b1;
   this.fname = fname;
   this.lineno = lineno;
   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot write to unimplemented virtual register \"%s\".", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();
`else
   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      path = parent.get_default_access();
   end
`endif

   foreach (fields[i]) begin
      vmm_ral_vfield f = fields[i];
      
      lsb = f.get_lsb_pos_in_register();
      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;
      foreach (f.XcbsX[j]) begin
         vmm_ral_vfield_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.pre_write(f, idx, tmp, path, domain);
      end
      value = (value & ~msk) | (tmp << lsb);
   end
   `vmm_callback(vmm_ral_vreg_callbacks,
                 pre_write(this, idx, value, path, domain));

   if(path == vmm_ral::BACKDOOR)
     addr = this.offset + idx;
   else
     addr = this.offset + (idx * this.incr);

   lsb = 0;
   status = vmm_rw::IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      vmm_rw::status_e s;

      msk = ((1<<(this.mem.get_n_bytes()*8))-1) << lsb;
      tmp = (value & msk) >> lsb;
      this.mem.write(s, addr + i, tmp,
                     path, domain ,
                     data_id, scenario_id, stream_id, fname, lineno);
      if (s != vmm_rw::IS_OK && s != vmm_rw::HAS_X) status = s;
      lsb += this.mem.get_n_bytes() * 8;
   end

   foreach (fields[i]) begin
      vmm_ral_vfield f = fields[i];
      
      lsb = f.get_lsb_pos_in_register();
      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;
      foreach (f.XcbsX[j]) begin
         vmm_ral_vfield_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.post_write(f, idx, tmp, path, domain, status);
      end
      value = (value & ~msk) | (tmp << lsb);
   end
   `vmm_callback(vmm_ral_vreg_callbacks,
                 post_write(this, idx, value, path, domain, status));

   `vmm_trace(this.log, $psprintf("Wrote virtual register \"%s\"[%0d] via %s with: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));
   this.write_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;

endtask: write


task vmm_ral_vreg::read(input  longint unsigned             idx,
                        output vmm_rw::status_e             status,
                        output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                        input  string                       domain = "",
                        input  int                          data_id = -1,
                        input  int                          scenario_id = -1,
                        input  int                          stream_id = -1,
                        input  string                       fname = "",
                        input  int                          lineno = 0);
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
   int lsb;
   this.read_in_progress = 1'b1;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot read from unimplemented virtual register \"%s\".", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (path == vmm_ral::DEFAULT) path = this.parent.get_default_access();
`else
   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      path = parent.get_default_access(); 
   end
`endif

   foreach (fields[i]) begin
      vmm_ral_vfield f = fields[i];
      foreach (f.XcbsX[j]) begin
         vmm_ral_vfield_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.pre_read(f, idx, path, domain);
      end
   end
  `vmm_callback(vmm_ral_vreg_callbacks,
                pre_read(this, idx, path, domain));

   if(path == vmm_ral::BACKDOOR)
     addr = this.offset + idx;
   else
     addr = this.offset + (idx * this.incr);

   lsb = 0;
   value = 0;
   status = vmm_rw::IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      vmm_rw::status_e s;

      this.mem.read(s, addr + i, tmp,
                     path, domain ,
                     data_id, scenario_id, stream_id, fname, lineno);
      if (s != vmm_rw::IS_OK && s != vmm_rw::HAS_X) status = s;

      value |= tmp << lsb;
      lsb += this.mem.get_n_bytes() * 8;
   end

   foreach (fields[i]) begin
      vmm_ral_vfield f = fields[i];

      lsb = f.get_lsb_pos_in_register();

      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;

      foreach (f.XcbsX[j]) begin
         vmm_ral_vfield_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.post_read(f, idx, tmp, path, domain, status);
      end

      value = (value & ~msk) | (tmp << lsb);
   end
   `vmm_callback(vmm_ral_vreg_callbacks,
                 post_read(this, idx, value, path, domain, status));

   `vmm_trace(this.log, $psprintf("Read virtual register \"%s\"[%0d] via %s: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));
   this.read_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;
endtask: read


task vmm_ral_vreg::poke(input longint unsigned              idx,
                        output vmm_rw::status_e             status,
                        input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  int                          data_id = -1,
                        input  int                          scenario_id = -1,
                        input  int                          stream_id = -1,
                        input  string                       fname = "",
                        input  int                          lineno = 0);
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
   int lsb;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot poke in unimplemented virtual register \"%s\".", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   status = vmm_rw::IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      vmm_rw::status_e s;

      msk = ((1<<(this.mem.get_n_bytes() * 8))-1) << lsb;
      tmp = (value & msk) >> lsb;

      this.mem.poke(status, addr + i, tmp,
                    data_id, scenario_id, stream_id, fname, lineno);
      if (s != vmm_rw::IS_OK && s != vmm_rw::HAS_X) status = s;

      lsb += this.mem.get_n_bytes() * 8;
   end

   `vmm_trace(this.log, $psprintf("Poked virtual register \"%s\"[%0d] with: 'h%h",
                                  this.get_fullname(), idx, value));
   this.fname = "";
   this.lineno = 0;

endtask: poke


task vmm_ral_vreg::peek(input longint unsigned              idx,
                        output vmm_rw::status_e             status,
                        output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  int                          data_id = -1,
                        input  int                          scenario_id = -1,
                        input  int                          stream_id = -1,
                        input  string                       fname = "",
                        input  int                          lineno = 0);
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr;
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
   int lsb;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot peek in from unimplemented virtual register \"%s\".", this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   value = 0;
   status = vmm_rw::IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      vmm_rw::status_e s;

      this.mem.peek(status, addr + i, tmp,
                    data_id, scenario_id, stream_id, fname, lineno);
      if (s != vmm_rw::IS_OK && s != vmm_rw::HAS_X) status = s;

      value |= tmp << lsb;
      lsb += this.mem.get_n_bytes() * 8;
   end

   `vmm_trace(this.log, $psprintf("Peeked virtual register \"%s\"[%0d]: 'h%h",
                                  this.get_fullname(), idx, value));
   this.fname = "";
   this.lineno = 0;

endtask: peek


function void vmm_ral_vreg::prepend_callback(vmm_ral_vreg_callbacks cb,
                                             string         fname = "",
                                             int            lineno = 0);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with virtual register \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Prepend new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_vreg::append_callback(vmm_ral_vreg_callbacks cb,
                                            string         fname = "",
                                            int            lineno = 0);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with virtual register \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Append new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_ral_vreg::unregister_callback(vmm_ral_vreg_callbacks cb);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         int j = i;
         // Unregister it
         this.callbacks.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with virtual register \"%s\"", this.get_fullname()));
endfunction: unregister_callback
