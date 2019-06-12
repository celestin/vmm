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


typedef class vmm_ral_vfield;

//------------------------------------------------------------------------------
// CLASS: vmm_ral_vfield_callbacks
// Field descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_vfield_callbacks extends vmm_ral_callbacks;
   string fname = "";
   int    lineno = 0;


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This callback method is invoked before a value is written to a field in the DUT. The written
   // value, if modified, changes the actual value that will be written. The path and domain
   // used to write to the field can also be modified. This callback method is only invoked
   // when the <vmm_ral_vfield::write()> or <vmm_ral_vreg::write()> method is used to
   // write to the field inside the DUT. This callback method is not invoked when the memory
   // location is directly written to using the <vmm_ral_mem::write()> method. Because
   // writing a field causes the memory location to be written, and, therefore all of the other
   // fields it contains to also be written, all registered <vmm_ral_vfield_callbacks::pre_write()>
   // methods with the fields contained in the same memory location will also be invoked.
   // Because the memory implementing the virtual field is accessed through its own abstraction
   // class, all of its registered <vmm_ral_mem_callbacks::pre_write()> methods will
   // also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task pre_write(vmm_ral_vfield                    field,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write


   //------------------------------------------------------------------------------
   // TASK: post_write
   // This callback method is invoked after a value is written to a virtual field in the DUT.
   // This callback method is only invoked when the <vmm_ral_vfield::write()> or <vmm_ral_vreg::write()>
   // method is used to write to the field inside the DUT. This callback method is not invoked
   // when the memory location is directly written to using the <vmm_ral_mem::write()>
   // method. Because writing a field causes the memory location to be written, and, therefore
   // all of the other fields it contains to also be written, all registered <vmm_ral_vfield_callbacks::post_write()>
   // methods with the fields contained in the same memory location will also be invoked.
   // Because the memory implementing the virtual field is accessed through its own abstraction
   // class, all of its registered <vmm_ral_mem_callbacks::post_write()> methods will
   // also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task post_write(vmm_ral_vfield                field,
                           longint unsigned              idx,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write


   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This callback method is invoked before a value is read from a field in the DUT. The path
   // and domain used to read from the field can be modified. This callback method is only invoked
   // when the <vmm_ral_vfield::read()> method is used to read the field inside the DUT.
   // This callback method is not invoked when the memory location containing the field is
   // read directly using the <vmm_ral_mem::read()> method. Because reading a field causes
   // the memory location to be read, and, therefore all of the other fields it contains to
   // also be read, all registered <vmm_ral_vfield_callbacks::pre_read()> methods with
   // the fields contained in the same memory location will also be invoked. Because the memory
   // implementing the virtual field is accessed through its own abstraction class, all
   // of its registered <vmm_ral_mem_callbacks::pre_read()> methods will also be invoked
   // as a side effect. 
   //------------------------------------------------------------------------------
   virtual task pre_read(vmm_ral_vfield        field,
                         longint unsigned      idx,
                         ref vmm_ral::path_e   path,
                         ref string            domain);
   endtask: pre_read


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This callback method is invoked after a value is read from a virtual field in the DUT.
   // The rdat and status values are the values that are ultimately returned by the <vmm_ral_vfield::read()>
   // method and they can be modified. This callback method is only invoked when the <vmm_ral_vfield::read()>
   // method is used to read the field inside the DUT. This callback method is not invoked when
   // the memory location containing the field is read directly using the <vmm_ral_mem::read()>
   // method. Because reading a field causes the memory location to be read, and, therefore
   // all of the other fields it contains to also be read, all registered <vmm_ral_vfield_callbacks::post_read()>
   // methods with the fields contained in the same memory location will also be invoked.
   // Because the memory implementing the virtual field is accessed through its own abstraction
   // class, all of its registered <vmm_ral_mem_callbacks::post_read()> methods will
   // also be invoked as a side effect. 
   //------------------------------------------------------------------------------
   virtual task post_read(vmm_ral_vfield                    field,
                          longint unsigned                  idx,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          vmm_ral::path_e                   path,
                          string                            domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_vfield_callbacks



//------------------------------------------------------------------------------
// CLASS: vmm_ral_vfield
// Field descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_vfield 
`ifdef VMM_RAL_BASE
     extends `VMM_RAL_BASE
`endif // VMM_RAL_BASE
;
   static vmm_log log = new("RAL", "virtual field");

   local string name;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   local vmm_ral_vreg parent;
`endif
   local int unsigned lsb;
   local int unsigned size;
   local string fname = "";
   local int lineno = 0;
   local bit read_in_progress;
   local bit write_in_progress;

   vmm_ral_vfield_callbacks XcbsX[$];

   extern /*local*/ function new(vmm_ral_vreg     parent,
                                 string           name,
                                 int unsigned     size,
                                 int unsigned     lsb_pos);


   //------------------------------------------------------------------------------
   // FUNCTION: get_name
   // Returns the name of the field corresponding to the instance of the descriptor. 
   //------------------------------------------------------------------------------
   extern virtual function string get_name();

   //------------------------------------------------------------------------------
   // FUNCTION: get_fullname
   // Returns the hierarchical name of the field corresponding to the instance of the descriptor.
   // The name of the top-level block or system is not included in the fully-qualified name
   // as it is implicit for every RAL model. 
   //------------------------------------------------------------------------------
   extern virtual function string get_fullname();

   //------------------------------------------------------------------------------
   // FUNCTION: get_register
   // Returns a reference to the descriptor of the virtual register that includes the field
   // corresponding to the descriptor instance. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_vreg get_register();

   //------------------------------------------------------------------------------
   // FUNCTION: get_lsb_pos_in_register
   // Returns the index of the least significant bit of the field in the virtual register that
   // instantiates it. An offset of 0 indicates a field that is aligned with the least-significant
   // bit of the virtual register. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_lsb_pos_in_register();

   //------------------------------------------------------------------------------
   // FUNCTION: get_n_bits
   // Returns the width, in number of bits, of the field. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_n_bits();


   //------------------------------------------------------------------------------
   // FUNCTION: get_access
   // Returns the specification of the behavior of the field when written and read through
   // the optionally-specified domain. If the register containing the field is shared across
   // multiple domains, a domain must be specified. The access mode of a field in a specific
   // domain may be restricted by the domain access rights of the memory implementing the
   // field. For example, a RW field may only be writable through one of the domains and read-only
   // through all of the other domains. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral::access_e get_access(string domain = "");


   //------------------------------------------------------------------------------
   // FUNCTION: display
   // Displays the image created by the <vmm_ral_field::psdisplay()> method on the standard
   // output. 
   //------------------------------------------------------------------------------
   extern virtual function void display(string prefix = "");

   //------------------------------------------------------------------------------
   // FUNCTION: psdisplay
   // Creates a human-readable description of the field and its current mirrored value.
   // Each line of the description is prefixed with the specified prefix. 
   //------------------------------------------------------------------------------
   extern virtual function string psdisplay(string prefix = "");


   //------------------------------------------------------------------------------
   // TASK: write
   // Writes the specified field value in the virtual register specified by the index into
   // the associated memory using the specified access path. If a back-door access path is
   // used, the effect of writing the field through a physical access is mimicked. For example,
   // a read-only field will not be written. If the virtual field is located in a memory shared
   // by more than one physical interface, a domain must be specified if a physical access
   // is used (front-door access). The optional value of the arguments: data_id scenario_id
   // stream_id 
   //------------------------------------------------------------------------------
   extern virtual task write(input  longint unsigned              idx,
                             output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                             input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id =- 1,
                             input  int                           stream_id = -1,
                             input  string                        fname = "",
                             input  int                           lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: read
   // Reads the current value of the field in the virtual register specified by the index from
   // the associated memory using the specified access path. If the field is located in a memory
   // shared by more than one physical interface, a domain must be specified if a physical
   // access is used (front-door access). The optional value of the arguments: data_id scenario_id
   // stream_id ...are passed to the back-door access method or used to set the corresponding
   // vmm_data class properties in the <vmm_rw_access> transaction descriptors that are
   // necessary to 
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
   // Deposit the specified field value in the associated memory using a back-door access.
   // The value of the field is updated, regardless of the access mode. The optional value
   // of the arguments: data_id scenario_id stream_id ...are passed to the back-door access
   // method. This allows the physical and back-door write accesses to be traced back to the
   // higher-level transaction that caused the access to occur. If the memory location where
   // this field is physically located contains other fields, the current value of the other
   // fields are peeked first then poked back in. 
   //------------------------------------------------------------------------------
   extern virtual task poke(input  longint unsigned              idx,
                            output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                           data_id = -1,
                            input  int                           scenario_id =- 1,
                            input  int                           stream_id = -1,
                            input  string                        fname = "",
                            input  int                           lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: peek
   // Peek the current value of the virtual field from the associated memory using a back-door
   // access. The value of the field in the design is not modified, regardless of the access
   // mode. The optional value of the arguments: data_id scenario_id stream_id ...are passed
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
   // this field descriptor. Callbacks are invoked in the reverse order of registration.
   // Note that field callback methods will be invoked before their corresponding <vmm_ral_vreg>
   // callback methods. 
   //------------------------------------------------------------------------------
   extern function void prepend_callback(vmm_ral_vfield_callbacks cb,
                                         string           fname = "",
                                         int              lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: append_callback
   // Appends the specified callback extension instance to the registered callbacks for
   // this field descriptor. Callbacks are invoked in the order of registration. Note that
   // field callback methods will be invoked before their corresponding <vmm_ral_vreg>
   // callback methods. 
   //------------------------------------------------------------------------------
   extern function void append_callback(vmm_ral_vfield_callbacks cb,
                                         string          fname = "",
                                         int             lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: unregister_callback
   // Removes the specified callback extension instance from the registered callbacks
   // for this field descriptor. A warning message is issued if the callback instance has
   // not been previously registered. 
   //------------------------------------------------------------------------------
   extern function void unregister_callback(vmm_ral_vfield_callbacks cb);
endclass: vmm_ral_vfield


function vmm_ral_vfield::new(vmm_ral_vreg      parent,
                             string            name,
                             int unsigned      size,
                             int unsigned      lsb_pos);
   `ifdef VMM_12_UNDERPIN_VMM_RAL
    super.new(parent, name);
    this.set_object_name(name, "RAL");
   `else
    this.parent = parent;
   `endif		
   this.name   = name;

   if (size == 0) begin
      `vmm_error(this.log, $psprintf("Virtual field \"%s\" cannot have 0 bits", this.get_fullname()));
      size = 1;
   end
   if (size > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Virtual field \"%s\" cannot have more than %0d bits",
                                     this.get_fullname(),
                                     `VMM_RAL_DATA_WIDTH));
      size = `VMM_RAL_DATA_WIDTH;
   end

   this.size   = size;
   this.lsb    = lsb_pos;

`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.register_field(this);
`else
   begin
      vmm_ral_vreg parent;
      $cast(parent, this._parent);
      parent.register_field(this); 
   end
`endif
endfunction: new


function string vmm_ral_vfield::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_vfield::get_fullname();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_fullname = {this.parent.get_fullname(), ".", this.name};
`else
   begin
      vmm_ral_vreg parent;
      $cast(parent, this._parent);
      get_fullname = {parent.get_fullname(), ".", this.name};
   end
`endif
endfunction: get_fullname


function vmm_ral_vreg vmm_ral_vfield::get_register();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_register = this.parent;
`else
   begin
      vmm_ral_vreg parent;
      $cast(parent, this._parent);
      get_register = parent; 
   end
`endif
endfunction: get_register


function int unsigned vmm_ral_vfield::get_lsb_pos_in_register();
   get_lsb_pos_in_register = this.lsb;
endfunction: get_lsb_pos_in_register


function int unsigned vmm_ral_vfield::get_n_bits();
   get_n_bits = this.size;
endfunction: get_n_bits


function vmm_ral::access_e vmm_ral_vfield::get_access(string domain = "");
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_vreg parent;
   $cast(parent, this._parent);
`endif

   if (parent.get_memory() == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::get_rights() on unimplemented virtual field \"%s\"",
                                     this.get_fullname()));
      return vmm_ral::RW;
   end

   get_access = parent.get_access(domain);
endfunction: get_access


function void vmm_ral_vfield::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display


function string vmm_ral_vfield::psdisplay(string prefix = "");
   string res_str = "";
   string t_str = "";
   bit with_debug_info = 1'b0;
   $sformat(psdisplay, {"%s%s[%0d-%0d]"}, prefix,
            this.get_name(),
            this.get_lsb_pos_in_register() + this.get_n_bits() - 1,
            this.get_lsb_pos_in_register());
   if (read_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay = {psdisplay, "\n", res_str, "currently executing read method"}; 
   end
   if ( write_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay = {psdisplay, "\n", res_str, "currently executing write method"}; 
   end

   foreach ( this.XcbsX[i]) begin
      if (this.XcbsX[i].fname != "" && this.XcbsX[i].lineno != 0) begin
         string tmp_str = "";
         with_debug_info = 1'b1;
         $sformat(tmp_str, "callback registered in %s:%0d\n",this.XcbsX[i].fname, this.XcbsX[i].lineno);
         res_str = {res_str, tmp_str};
      end
   end
   if (XcbsX.size() != 0) begin
      $sformat(t_str, "\nTotal %0d callbacks have been registered for %s",XcbsX.size(), this.get_name());
      psdisplay= {psdisplay, t_str};
   end
   if (with_debug_info == 1'b1) begin
      psdisplay= {psdisplay, "\ncallbacks with debug info.."};
      psdisplay= {psdisplay, "\n", res_str };
   end
endfunction: psdisplay


task vmm_ral_vfield::write(input  longint unsigned              idx,
                           output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                           input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1,
                           input  string                        fname = "",
                           input  int                           lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, fmsb, rmwbits;
   int segsiz, segn;
   vmm_ral_mem    mem;
   vmm_ral::path_e rm_path;
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_vreg parent;
   $cast(parent, this._parent);
`endif


   this.fname = fname;
   this.lineno = lineno;

   write_in_progress = 1'b1;
   mem = parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::write() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block blk = parent.get_block();
      path = blk.get_default_access();
   end

   status = vmm_rw::IS_OK;

   parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("Writing value 'h%h that is greater than field \"%s\" size (%0d bits)", value, this.get_fullname(), this.get_n_bits()));
      value &= value & ((1<<this.size)-1);
   end
   tmp = 0;

   foreach (this.XcbsX[j]) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.pre_write(this, idx, value, path, domain);
   end

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = parent.get_offset_in_memory(idx) + (flsb / segsiz);

   // Favor backdoor read to frontdoor read for the RMW operation
   rm_path = vmm_ral::DEFAULT;
   if (mem.get_backdoor() != null) rm_path = vmm_ral::BACKDOOR;

   // Any bits on the LSB side we need to RMW?
   rmwbits = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (rmwbits + this.get_n_bits() - 1) / segsiz + 1;

   if (rmwbits > 0) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] segn;

      mem.read(st, segoff, tmp, rm_path, domain,
               data_id, scenario_id, stream_id, fname, lineno);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) begin
         `vmm_error(this.log,
                    $psprintf("Unable to read LSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                              mem.get_fullname(), segoff, this.get_fullname()));
         status = vmm_rw::ERROR;
         parent.XatomicX(0);
         return;
      end

      value = (value << rmwbits) | (tmp & ((1<<rmwbits)-1));
   end

   // Any bits on the MSB side we need to RMW?
   fmsb = rmwbits + this.get_n_bits() - 1;
   rmwbits = (fmsb+1) % segsiz;
   if (rmwbits > 0) begin
      if (segn > 0) begin
         mem.read(st, segoff + segn - 1, tmp, rm_path, domain,
                  data_id, scenario_id, stream_id, fname, lineno);
         if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) begin
            `vmm_error(this.log,
                       $psprintf("Unable to read MSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                                 mem.get_fullname(), segoff+segn-1,
                                 this.get_fullname()));
            status = vmm_rw::ERROR;
            parent.XatomicX(0);
            return;
         end
      end
      value |= (tmp & ~((1<<rmwbits)-1)) << ((segn-1)*segsiz);
   end

   // Now write each of the segments
   tmp = value;
   repeat (segn) begin
      mem.write(st, segoff, tmp, path, domain,
               data_id, scenario_id, stream_id, fname, lineno);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) status = vmm_rw::ERROR;

      segoff++;
      tmp = tmp >> segsiz;
   end

   foreach (this.XcbsX[j]) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.post_write(this, idx, value, path, domain, status);
   end

   parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Wrote virtual field \"%s\"[%0d] via %s with: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   write_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;
endtask: write


task vmm_ral_vfield::read(input longint unsigned              idx,
                          output vmm_rw::status_e             status,
                          output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                          input  string                       domain = "",
                          input  int                          data_id = -1,
                          input  int                          scenario_id = -1,
                          input  int                          stream_id = -1,
                          input  string                       fname = "",
                          input  int                          lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, lsb;
   int segsiz, segn;
   vmm_ral_mem    mem;
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_vreg parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;

   read_in_progress = 1'b1;
   mem = parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::read() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   if (path == vmm_ral::DEFAULT) begin
      vmm_ral_block blk = parent.get_block();
      path = blk.get_default_access();
   end

   status = vmm_rw::IS_OK;

   parent.XatomicX(1);

   value = 0;

   foreach (this.XcbsX[j]) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.pre_read(this, idx, path, domain);
   end

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = parent.get_offset_in_memory(idx) + (flsb / segsiz);
   lsb = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (lsb + this.get_n_bits() - 1) / segsiz + 1;

   // Read each of the segments, MSB first
   segoff += segn - 1;
   repeat (segn) begin
      value = value << segsiz;

      mem.read(st, segoff, tmp, path, domain,
               data_id, scenario_id, stream_id, fname, lineno);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) status = vmm_rw::ERROR;

      segoff--;
      value |= tmp;
   end

   // Any bits on the LSB side we need to get rid of?
   value = value >> lsb;

   // Any bits on the MSB side we need to get rid of?
   value &= (1<<this.get_n_bits()) - 1;

   foreach (this.XcbsX[j]) begin
      vmm_ral_vfield_callbacks cb;
      if (!$cast(cb, this.XcbsX[j])) continue;
      cb.post_read(this, idx, value, path, domain, status);
   end

   parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Read virtual field \"%s\"[%0d] via %s: 'h%h",
                                  this.get_fullname(), idx,
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   read_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;
endtask: read
               

task vmm_ral_vfield::poke(input  longint unsigned              idx,
                          output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1,
                          input  string                        fname = "",
                          input  int                           lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, fmsb, rmwbits;
   int segsiz, segn;
   vmm_ral_mem    mem;
   vmm_ral::path_e rm_path;

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_vreg parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;

   mem = parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::poke() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   status = vmm_rw::IS_OK;

   parent.XatomicX(1);

   if (value >> this.size) begin
      `vmm_warning(log, $psprintf("Writing value 'h%h that is greater than field \"%s\" size (%0d bits)", value, this.get_fullname(), this.get_n_bits()));
      value &= value & ((1<<this.size)-1);
   end
   tmp = 0;

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = parent.get_offset_in_memory(idx) + (flsb / segsiz);

   // Any bits on the LSB side we need to RMW?
   rmwbits = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (rmwbits + this.get_n_bits() - 1) / segsiz + 1;

   if (rmwbits > 0) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] segn;

      mem.peek(st, segoff, tmp,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) begin
         `vmm_error(this.log,
                    $psprintf("Unable to read LSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                              mem.get_fullname(), segoff, this.get_fullname()));
         status = vmm_rw::ERROR;
         parent.XatomicX(0);
         return;
      end

      value = (value << rmwbits) | (tmp & ((1<<rmwbits)-1));
   end

   // Any bits on the MSB side we need to RMW?
   fmsb = rmwbits + this.get_n_bits() - 1;
   rmwbits = (fmsb+1) % segsiz;
   if (rmwbits > 0) begin
      if (segn > 0) begin
         mem.peek(st, segoff + segn - 1, tmp,
                  data_id, scenario_id, stream_id, fname, lineno);
         if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) begin
            `vmm_error(this.log,
                       $psprintf("Unable to read MSB bits in %s[%0d] to for RMW cycle on virtual field %s.",
                                 mem.get_fullname(), segoff+segn-1,
                                 this.get_fullname()));
            status = vmm_rw::ERROR;
            parent.XatomicX(0);
            return;
         end
      end
      value |= (tmp & ~((1<<rmwbits)-1)) << ((segn-1)*segsiz);
   end

   // Now write each of the segments
   tmp = value;
   repeat (segn) begin
      mem.poke(st, segoff, tmp,
               data_id, scenario_id, stream_id, fname, lineno);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) status = vmm_rw::ERROR;

      segoff++;
      tmp = tmp >> segsiz;
   end

   parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Wrote virtual field \"%s\"[%0d] with: 'h%h",
                                  this.get_fullname(), idx, value));

   this.fname = "";
   this.lineno = 0;
endtask: poke


task vmm_ral_vfield::peek(input  longint unsigned             idx,
                          output vmm_rw::status_e             status,
                          output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  int                          data_id = -1,
                          input  int                          scenario_id = -1,
                          input  int                          stream_id = -1,
                          input  string                       fname = "",
                          input  int                          lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
   bit [`VMM_RAL_DATA_WIDTH-1:0] segval;
   bit [`VMM_RAL_ADDR_WIDTH-1:0] segoff;
   vmm_rw::status_e st;

   int flsb, lsb;
   int segsiz, segn;
   vmm_ral_mem    mem;

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_vreg parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;

   mem = parent.get_memory();
   if (mem == null) begin
      `vmm_error(this.log, $psprintf("Cannot call vmm_ral_vfield::peek() on unimplemented virtual register \"%s\"",
                                     this.get_fullname()));
      status = vmm_rw::ERROR;
      return;
   end

   status = vmm_rw::IS_OK;

   parent.XatomicX(1);

   value = 0;

   segsiz = mem.get_n_bytes() * 8;
   flsb    = this.get_lsb_pos_in_register();
   segoff  = parent.get_offset_in_memory(idx) + (flsb / segsiz);
   lsb = flsb % segsiz;

   // Total number of memory segment in this field
   segn = (lsb + this.get_n_bits() - 1) / segsiz + 1;

   // Read each of the segments, MSB first
   segoff += segn - 1;
   repeat (segn) begin
      value = value << segsiz;

      mem.peek(st, segoff, tmp,
               data_id, scenario_id, stream_id);
      if (st != vmm_rw::IS_OK && st != vmm_rw::HAS_X) status = vmm_rw::ERROR;

      segoff--;
      value |= tmp;
   end

   // Any bits on the LSB side we need to get rid of?
   value = value >> lsb;

   // Any bits on the MSB side we need to get rid of?
   value &= (1<<this.get_n_bits()) - 1;

   parent.XatomicX(0);

   `vmm_trace(this.log, $psprintf("Peeked virtual field \"%s\"[%0d]: 'h%h",
                                  this.get_fullname(), idx, value));

   this.fname = "";
   this.lineno = 0;
endtask: peek
               

function void vmm_ral_vfield::prepend_callback(vmm_ral_vfield_callbacks cb,
                                               string           fname = "",
                                               int              lineno = 0);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Prepend new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.XcbsX.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_vfield::append_callback(vmm_ral_vfield_callbacks cb,
                                              string           fname = "",
                                              int              lineno = 0);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with field \"%s\"", this.get_fullname()));
         return;
      end
   end
   
   // Append new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.XcbsX.push_back(cb);
endfunction: append_callback


function void vmm_ral_vfield::unregister_callback(vmm_ral_vfield_callbacks cb);
   foreach (this.XcbsX[i]) begin
      if (this.XcbsX[i] == cb) begin
         int j = i;
         // Unregister it
         this.XcbsX.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with field \"%s\"", this.get_fullname()));
endfunction: unregister_callback
