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



//------------------------------------------------------------------------------
// CLASS: vmm_ral_reg_callbacks
// Base class for register descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_reg_callbacks extends vmm_ral_callbacks;
   string fname = "";
   int lineno = 0;


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This callback method is invoked before a value is written to a register in the DUT. The
   // written value, if modified, changes the actual value that is written. The path and domain
   // used to write to the register can also be modified. This callback method is only invoked
   // when the <vmm_ral_reg::write> or <vmm_ral_field::write> method is used to write
   // to the register inside the DUT. This callback method is not invoked when only the mirrored
   // value is written to using the <vmm_ral_reg::set> method. Because writing a register
   // causes all of the fields it contains to be written, all registered <vmm_ral_field_callbacks::pre_write>
   // methods with the fields contained in the register will also be invoked before all registered
   // register callback methods. 
   //------------------------------------------------------------------------------
   virtual task pre_write(vmm_ral_reg                       rg,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                          ref vmm_ral::path_e               path,
                          ref string                        domain);
   endtask: pre_write


   //------------------------------------------------------------------------------
   // TASK: post_write
   // This callback method is invoked after a value is successfully written to a register
   // in the DUT. The wdat value is the final mirrored value in the register as reported by the
   // <vmm_ral_reg::get> method. If a physical write access did not return vmm_rw::IS_OK,
   // this method is not called. This callback method is only invoked when the <vmm_ral_reg::write>
   // or <vmm_ral_field::write> method is used to write to the register inside the DUT.
   // This callback method is not invoked when only the mirrored value is written to using
   // the <vmm_ral_reg::set> method. 
   //------------------------------------------------------------------------------
   virtual task post_write(vmm_ral_reg                   rg,
                           bit [`VMM_RAL_DATA_WIDTH-1:0] wdat,
                           vmm_ral::path_e               path,
                           string                        domain,
                           ref vmm_rw::status_e          status);
   endtask: post_write


   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This callback method is invoked before a value is read from a register in the DUT. You
   // can modify the path and domain used to read the register. This callback method is only
   // invoked when the <vmm_ral_reg::read> or the <vmm_ral_field::read> method is
   // used to read from the register inside the DUT. This callback method is not invoked when
   // only the mirrored value is read using the <vmm_ral_reg::get> method. Because reading
   // a register causes all of the fields it contains to be read, all registered <vmm_ral_field_callbacks::pre_read>
   // methods with the fields contained in the register will also be invoked before all registered
   // register callback methods. 
   //------------------------------------------------------------------------------
   virtual task pre_read(vmm_ral_reg          rg,
                         ref vmm_ral::path_e  path,
                         ref string           domain);
   endtask: pre_read


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This callback method is invoked after a value is successfully read from a register in
   // the DUT. The rdat and status values are the values that will be ultimately returned by
   // the <vmm_ral_reg::read> method and can be modified. If a physical read access did
   // not return vmm_rw::IS_OK, this method is not called. This callback method is invoked
   // only when the <vmm_ral_reg::read> or <vmm_ral_field::read> method is used to
   // read from the register inside the DUT. This callback method is not invoked when only
   // the mirrored value is read from using the <vmm_ral_reg::get> method. 
   //------------------------------------------------------------------------------
   virtual task post_read(vmm_ral_reg                       rg,
                          ref bit [`VMM_RAL_DATA_WIDTH-1:0] rdat,
                          input vmm_ral::path_e             path,
                          input string                      domain,
                          ref vmm_rw::status_e              status);
   endtask: post_read
endclass: vmm_ral_reg_callbacks



//------------------------------------------------------------------------------
// CLASS: vmm_ral_reg_frontdoor
// Virtual base class for user-defined access to registers through a physical interface.
// By default, different registers are mapped to different addresses in the address space
// of the block instantiating them. If registers are physically accessed using a non-linear,
// non-mapped mechanism, this base class must be user-extended to provide the physical
// access to these registers. 
//------------------------------------------------------------------------------
virtual class vmm_ral_reg_frontdoor;
   static vmm_log log = new("vmm_ral_reg_frontdoor", "class");
   string fname = "";
   int lineno = 0;
   

   //------------------------------------------------------------------------------
   // TASK: write
   // Performs a physical write access to the register corresponding to the instance of this
   // class. Returns an indication of the success of the operation. The values of the arguments:
   // data_id scenario_id stream_id ...are the values that were optionally specified to
   // the <vmm_ral_reg::write> method call that requires the front-door access. This
   // allows the write access to be traced back to the higher-level transaction that caused
   // the access to occur. 
   //------------------------------------------------------------------------------
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1
                            );

   //------------------------------------------------------------------------------
   // TASK: read
   // Performs a physical read access of the register corresponding to the instance of this
   // class. Returns the content of the register and an indication of the success of the operation.
   // The values of the arguments: data_id scenario_id stream_id ...are the values that
   // were optionally specified to the <vmm_ral_reg::read> method call that requires
   // the front-door access. This allows the read access to be traced back to the higher-level
   // transaction that caused the access to occur. 
   //------------------------------------------------------------------------------
   extern virtual task read(output vmm_rw::status_e              status,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1
                           );
endclass: vmm_ral_reg_frontdoor




//------------------------------------------------------------------------------
// CLASS: vmm_ral_reg
// Base class for register descriptors. 
//------------------------------------------------------------------------------
class vmm_ral_reg 
`ifdef VMM_RAL_BASE
extends `VMM_RAL_BASE
`endif // VMM_RAL_BASE
;
   static vmm_log log = new("RAL", "register");

   static vmm_ral_reg all_regs[`VMM_AA_INT]; // Keeps track of all registers in the RAL Model
   static local int unsigned reg_id_factory = 0;
   local int unsigned reg_id = 0;
   local bit locked;
`ifndef VMM_12_UNDERPIN_VMM_RAL
   local vmm_ral_block parent;
`endif
   local string name;
   local int unsigned  n_bits;
   local int unsigned  n_used_bits;

   local logic [`VMM_RAL_ADDR_WIDTH-1:0] offset_in_block[];
   local string                          domains[];
   local vmm_ral::access_e               rights[];

   local vmm_ral_field fields[$];   // Fields in LSB to MSB order
   local string        constr[];
   local event         value_change;

   local vmm_ral_access        ral_access;
   local vmm_ral_reg_frontdoor frontdoor[];
   local vmm_ral_reg_backdoor  backdoor;

   local vmm_ral_reg_callbacks callbacks[$];

   local string attributes[string];

   local int has_cover;
   local int cover_on;

   local semaphore atomic;
   local string fname = "";
   local int lineno = 0;
   local bit read_in_progress = 0;
   local bit write_in_progress = 0;

   /*local*/ bit Xis_busyX;
   /*local*/ bit Xis_locked_by_fieldX;

   extern function new(vmm_ral_block                 parent,
                       string                        name,
                       int unsigned                  n_bits,
                       bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                       string                        domain = "",
                       int                           cover_on = vmm_ral::NO_COVERAGE,
                       bit [1:0]                     rights = 2'b11,
                       bit                           unmapped = 0,
                       int                           has_cover = vmm_ral::NO_COVERAGE);

   /*local*/ extern function void Xlock_modelX();
   /*local*/ extern function void add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                             string                        domain,
                                             bit [1:0]                     rights,
                                             bit                           unmapped = 0);
   
   local virtual function void domain_coverage(string domain,
                                               bit    rights,
                                               int    idx);
   endfunction
   
   /*local*/ extern function void register_field(vmm_ral_field field);
   /*local*/ extern function void Xregister_ral_accessX(vmm_ral_access access);
   /*local*/ extern function void Xadd_constraintsX(string name);
   /*local*/ extern task XatomicX(bit on);
   /*local*/ extern task XwriteX(output vmm_rw::status_e             status,
                                 input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                 input  vmm_ral::path_e              path,
                                 input  string                       domain,
                                 input  int                          data_id,
                                 input  int                          scenario_id,
                                 input  int                          stream_id,
                                 input  string                       fname = "",
                                 input  int                          lineno = 0);
   /*local*/ extern task XreadX(output vmm_rw::status_e             status,
                                output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                                input  vmm_ral::path_e              path,
                                input  string                       domain,
                                input  int                          data_id,
                                input  int                          scenario_id,
                                input  int                          stream_id,
                                input  string                       fname = "",
                                input  int                          lineno = 0);
   

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
   // FUNCTION: get_n_domains
   // Returns the number of domains that share this register. You can obtain the name of the
   // domains with the <vmm_ral_reg::get_domains> method. 
   //------------------------------------------------------------------------------
   extern virtual function int get_n_domains();
   extern virtual function vmm_ral_block get_parent();

   //------------------------------------------------------------------------------
   // FUNCTION: get_domains
   // Fills the specified dynamic array with the names of all the block-level domains that
   // can access this register. The order of the domain names is not specified. 
   //------------------------------------------------------------------------------
   extern virtual function void get_domains(ref string domains[]);

   //------------------------------------------------------------------------------
   // FUNCTION: get_rights
   // Returns the access rights of a register. Returns vmm_ral::RW, vmm_ral::RO, or vmm_ral::WO.
   // The access rights of a register is always vmm_ral::RW, unless it is a shared register
   // with access restriction in a particular domain. If the register is shared in more than
   // one domain, a domain name must be specified. If the register is not shared in the specified
   // domain, an error message is issued and vmm_ral::RW is returned. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral::access_e get_rights(string domain = "");

   //------------------------------------------------------------------------------
   // FUNCTION: get_block
   // Returns a reference to the descriptor of the block that includes the register corresponding
   // to the descriptor instance. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_block get_block();
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_offset_in_block(string domain = ""); 
   extern virtual function bit [`VMM_RAL_ADDR_WIDTH-1:0] get_address_in_system(string domain = "");

   //------------------------------------------------------------------------------
   // FUNCTION: get_n_bytes
   // Returns the width, in number of bytes, of the register. 
   //------------------------------------------------------------------------------
   extern virtual function int unsigned get_n_bytes();

   //------------------------------------------------------------------------------
   // FUNCTION: get_constraints
   // Fills the specified dynamic array with the names of the constraint blocks in this register.
   // The constraint blocks in the fields within this register are specified in constraint
   // blocks with the same name as the field name. The location of each constraint block name
   // in the array is not defined. 
   //------------------------------------------------------------------------------
   extern virtual function void get_constraints(ref string names[]);


   //------------------------------------------------------------------------------
   // FUNCTION: display
   // Displays the image created by the <vmm_ral_reg::psdisplay> method to the standard
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
   // Fills the specified dynamic array with the descriptor for all of the fields contained
   // in the register. Fields are ordered from least-significant position to most-significant
   // position within the register. 
   //------------------------------------------------------------------------------
   extern virtual function void get_fields(ref vmm_ral_field fields[]);

   //------------------------------------------------------------------------------
   // FUNCTION: get_field_by_name
   // Finds a field with the specified name in the register and returns its descriptor. If
   // no fields are found, returns null. 
   //------------------------------------------------------------------------------
   extern virtual function vmm_ral_field get_field_by_name(string name);


   //------------------------------------------------------------------------------
   // FUNCTION: set_attribute
   // Set the specified attribute to the specified value for this register. If the value is
   // specified as "", the specified attribute is deleted. A warning is issued if an existing
   // attribute is modified. Attribute names are case sensitive. 
   //------------------------------------------------------------------------------
   extern virtual function void set_attribute(string name,
                                              string value);

   //------------------------------------------------------------------------------
   // FUNCTION: get_attribute
   // Get the value of the specified attribute for this register. If the attribute does not
   // exists, "" is returned. If the "inherited" argument is specifed as TRUE, the value of
   // the attribute is inherited from the nearest enclosing block or system if it is not specified
   // for this register. If it is specified as FALSE, the value "" is returned if it does not
   // exists in the this register. Attribute names are case sensitive. 
   //------------------------------------------------------------------------------
   extern virtual function string get_attribute(string name,
                                                bit inherited = 1);

   //------------------------------------------------------------------------------
   // FUNCTION: get_all_attributes
   // Return an array filled with the name of the attributes defined for this register. If
   // the "inherited" argument is specifed as TRUE, the value of all attributes inherited
   // from the enclosing block and system(s) is included. If the argument is specified as
   // FALSE, only the attributed defined for this register are returned. The order in which
   // attribute names are returned is not specified. 
   //------------------------------------------------------------------------------
   extern virtual function void get_all_attributes(ref string names[],
                                                   input bit inherited = 1);

   extern virtual function bit can_cover(int models);
   extern virtual function int set_cover(int is_on);
   extern virtual function bit is_cover_on(int is_on);

   extern local virtual function void XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                              vmm_ral::path_e               path,
                                              string                        domain);
   extern local virtual function void XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                              vmm_ral::path_e               path,
                                              string                        domain);

   //------------------------------------------------------------------------------
   // FUNCTION: set
   // Sets the mirror value of the fields in the register to the specified value. Does not actually
   // set the value of the register in the design, only the value mirrored in its corresponding
   // descriptor in the RAL model. Use the <vmm_ral_reg::update> method to update the
   // actual register with the mirrored value or the <vmm_ral_reg::write> method to set
   // the actual register and its mirrored value. See <vmm_ral_field::set> 
   // for more information on the effect of setting mirror values on fields with different
   // access modes. To modify the mirrored field values to a specific value, regardless of
   // the access modes--and thus use the RAL mirror as a scoreboard for the register values
   // in the DUT--use the <vmm_ral_reg::predict> method. 
   //------------------------------------------------------------------------------
   extern virtual function void set(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                    string                        fname = "",
                                    int                           lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: predict
   // Force the mirror value of the fields in the register to the specified value. Does not
   // actually force the value of the fields in the design, only the value mirrored in their
   // corresponding descriptor in the RAL model. Use the <vmm_ral_reg::update> method
   // to update the actual register with the mirrored value or the <vmm_ral_reg::write>
   // method to set the register and its mirrored value. The final value in the mirror is the
   // specified value, regardless of the access mode of the fields in the register. For example,
   // the mirrored value of a read-only field is modified by this method, and the mirrored
   // value of a read-update field can be updated to any value predicted to correspond to the
   // value in the corresponding physical bits in the design. By default, predict does not
   // allow any update of the mirror, when RAL is busy executing a transaction on this register.
   // However, if need be, that can be overridden by setting the force_predict argument to
   // 1. 
   //------------------------------------------------------------------------------
   extern virtual function bit predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                       string                        fname = "",
                                       int                           lineno = 0, 
                                       bit                           force_predict = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: get
   // Returns the mirror value of the fields in the register. Does not actually read the value
   // of the register in the design, only the value mirrored in its corresponding descriptor
   // in the RAL model. If the register contains write-only fields, the mirrored value for
   // those fields are the value last written and assumed to reside in the bits implementing
   // these fields. Although a physical read operation would return zeroes for these fields,
   // the returned mirrored value is the actual content. Use the <vmm_ral_reg::read>
   // method to get the actual register value. 
   //------------------------------------------------------------------------------
   extern virtual function bit[`VMM_RAL_DATA_WIDTH-1:0] get(string  fname = "",
                                                            int     lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: reset
   // Sets the mirror value of the fields in the register to the specified reset value. Does
   // not actually reset the value of the register in the design, only the value mirrored in
   // the descriptor in the RAL model. Write-once fields in the register can be modified after
   // a hard reset operation. 
   //------------------------------------------------------------------------------
   extern virtual function void reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   extern virtual function logic [`VMM_RAL_DATA_WIDTH-1:0]
                    get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);

   //------------------------------------------------------------------------------
   // FUNCTION: needs_update
   // If a mirror value has been modified in the RAL model without actually updating the actual
   // register, the mirror and state of the register is outdated. This method returns TRUE
   // if the state of the register needs to be updated to match the mirrored values (or vice-versa).
   // The mirror values or actual content of registers are not modified. See <vmm_ral_reg::update>
   // or <vmm_ral_reg::mirror> for more details. 
   //------------------------------------------------------------------------------
   extern virtual function bit needs_update(); 
 

   //------------------------------------------------------------------------------
   // TASK: update
   // Updates the content of the register in the design to match the mirrored value, if it has
   // been modified using one of the set() methods to a different value. The update can be performed
   // using the physical interfaces (frontdoor) or <vmm_ral_reg::poke> (backdoor).
   // If the register is shared across multiple physical interfaces and physical access
   // is used (front-door access), a domain must be specified. This method performs the reverse
   // operation of <vmm_ral_reg::mirror> . 
   //------------------------------------------------------------------------------
   extern virtual task update(output vmm_rw::status_e status,
                              input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                              input  string           domain = "");

   //------------------------------------------------------------------------------
   // TASK: write
   // Writes the specified value in the register in the design using the specified access
   // path. If the register is shared by more than one physical interface, a domain must be
   // specified if a physical access is used (front-door access). If a back-door access path
   // is used, the effect of writing the register through a physical access is mimicked. For
   // example, read-only bits in the registers will not be written. The optional value of
   // the arguments: 
   //------------------------------------------------------------------------------
   extern virtual task write(output vmm_rw::status_e             status,
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
   // Reads the current value of the register from the design using the specified access path.
   // If the register is shared by more than one physical interface, a domain must be specified
   // if a physical access is used (front-door access). If a back-door access path is used,
   // the effect of reading the register through a physical access is mimicked. For example,
   // clear-on-read bits in the registers will be cleared. The optional value of the arguments:
   // 
   //------------------------------------------------------------------------------
   extern virtual task read(output vmm_rw::status_e             status,
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
   // Deposit the specified value in the register in the design, as-is, using a back-door
   // access. See <vmm_ral_field::poke> for a description of the effect on field values.
   // The optional value of the arguments: data_id scenario_id stream_id ...are passed
   // to the back-door access method. This allows the physical and back-door write access
   // to be traced back to the higher-level transaction that caused the access to occur. 
   //------------------------------------------------------------------------------
   extern virtual task poke(output vmm_rw::status_e             status,
                            input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: peek
   // Reads the current value of the register from the design using a back-door access. The
   // optional value of the arguments: data_id scenario_id stream_id ...are passed to the
   // back-door access method. This allows the physical and back-door read access to be traced
   // back to the higher-level transaction that caused the access to occur. 
   //------------------------------------------------------------------------------
   extern virtual task peek(output vmm_rw::status_e             status,
                            output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                            input  int                          data_id = -1,
                            input  int                          scenario_id = -1,
                            input  int                          stream_id = -1,
                            input  string                       fname = "",
                            input  int                          lineno = 0);

   //------------------------------------------------------------------------------
   // TASK: mirror
   // Updates the content of the register mirror value to match the corresponding value in
   // the design. The mirroring can be performed using the physical interfaces (frontdoor)
   // or <vmm_ral_reg::peek> (backdoor). If the check argument is specified as vmm_ral::VERB,
   // an error message is issued if the current mirrored value does not match the actual value
   // in the design. If the register is shared across multiple physical interfaces and physical
   // access is used (front-door access), a domain must be specified. If the register contains
   // write-only fields, their content is mirrored and optionally checked only if a vmm_ral::BACKDOOR
   // access path is used to read the register. 
   //------------------------------------------------------------------------------
   extern virtual task mirror(output vmm_rw::status_e status,
                              input vmm_ral::check_e  check  = vmm_ral::QUIET,
                              input vmm_ral::path_e   path = vmm_ral::DEFAULT,
                              input string            domain = "",
                              input  string           fname = "",
                              input  int              lineno = 0);
  

   //------------------------------------------------------------------------------
   // FUNCTION: set_frontdoor
   // By default, registers are mapped linearly into the address space of the block that instantiates
   // them. If registers are accessed using a different mechanism, a user-defined access
   // mechanism must be defined and associated with the corresponding register abstraction
   // class. See "User-Defined Register Access" for an example. 
   //------------------------------------------------------------------------------
   extern function void set_frontdoor(vmm_ral_reg_frontdoor ftdr,
                                      string                domain = "",
                                      string                fname = "",
                                      int                   lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: get_frontdoor
   // Returns the current user-defined mechanism for this register for the specified domain.
   // If null, no user-defined mechanism has been defined. A user-defined mechanism is defined
   // by using the <vmm_ral_reg::set_frontdoor> method. 
   //------------------------------------------------------------------------------
   extern function vmm_ral_reg_frontdoor get_frontdoor(string domain = "");

   //------------------------------------------------------------------------------
   // FUNCTION: set_backdoor
   // Registers implemented using SystemVerilog variables can be accessed using a hierarchical
   // path. This direct back-door access is automatically generated if the necessary hdl_path
   // properties are specified in the RALF description. However, registers can be modeled
   // using other methods, or be included in imported models written in different languages.
   // This method is used to associate a back-door access mechanism with a register descriptor
   // to enable back-door accesses. 
   //------------------------------------------------------------------------------
   extern function void set_backdoor(vmm_ral_reg_backdoor bkdr,
                                     string               fname = "",
                                     int                  lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: get_backdoor
   // Returns the current back-door mechanism for this register. If null, no back-door mechanism
   // has been defined. A back-door mechanism can be automatically defined by using the hdl_path
   // properties in the RALF definition or user-defined using the <vmm_ral_reg::set_backdoor>
   // method. 
   //------------------------------------------------------------------------------
   extern function vmm_ral_reg_backdoor get_backdoor();


   //------------------------------------------------------------------------------
   // FUNCTION: prepend_callback
   // Prepends the specified callback extension instance to the registered callbacks for
   // this register descriptor. Callbacks are invoked in the reverse order of registration.
   // Note that the corresponding <vmm_ral_field" callback methods will be invoked before
   // the register callback methods. 
   //------------------------------------------------------------------------------
   extern function void prepend_callback(vmm_ral_reg_callbacks cb,
                                         string                fname = "",
                                         int                   lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: append_callback
   // Appends the specified callback extension instance to the registered callbacks for
   // this register descriptor. Callbacks are invoked in the order of registration. Note
   // that the corresponding <vmm_ral_field" callback methods will be invoked before the
   // register callback methods. 
   //------------------------------------------------------------------------------
   extern function void append_callback(vmm_ral_reg_callbacks cb,
                                        string                fname = "",
                                        int                   lineno = 0);

   //------------------------------------------------------------------------------
   // FUNCTION: unregister_callback
   // Removes the specified callback extension instance from the registered callbacks
   // for this register descriptor. A warning message is issued if the callback instance
   // has not been previously registered. 
   //------------------------------------------------------------------------------
   extern function void unregister_callback(vmm_ral_reg_callbacks cb);

   extern local function int get_domain_index(string domain);
   extern virtual local function void sample(bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                             bit                           is_read,
                                             int                           domain);

   extern function int unsigned get_reg_ID();


   //------------------------------------------------------------------------------
   // FUNCTION: sample_field_values
   // By using this function, you can sample the field value coverage within the RAL registers.
   // With this method, you will be able to sample field values within the RAL register itself
   // which would sample field coverage for all the fields within the register by calling
   // field_values.sample() for the register. 
   //------------------------------------------------------------------------------
   extern virtual function void sample_field_values();
endclass: vmm_ral_reg


function vmm_ral_reg::new(vmm_ral_block                 parent,
                          string                        name,
                          int unsigned                  n_bits,
                          bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                          string                        domain = "",
                          int                           cover_on = vmm_ral::NO_COVERAGE,
                          bit [1:0]                     rights = 2'b11,
                          bit                           unmapped = 0,
                          int                           has_cover = vmm_ral::NO_COVERAGE);
   `ifdef VMM_12_UNDERPIN_VMM_RAL
     super.new(parent, name);
     this.set_object_name(name, "RAL");
   `else 
     this.parent = parent;
   `endif		
   this.locked = 0;

`ifndef VMM_12_UNDERPIN_VMM_RAL
   this.parent.register_reg(this);
`else
   begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      parent.register_reg(this); 
   end
`endif

   this.name = name;
   this.has_cover = has_cover;
   this.cover_on = vmm_ral::NO_COVERAGE;
   void'(this.set_cover(cover_on));

   if (n_bits == 0) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" cannot have 0 bits", this.get_name()));
      n_bits = 1;
   end
   if (n_bits > `VMM_RAL_DATA_WIDTH) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" cannot have more than %0d bits (%0d)", this.get_name(), `VMM_RAL_DATA_WIDTH, n_bits));
      n_bits = `VMM_RAL_DATA_WIDTH;
   end
   this.n_bits = n_bits;
   this.n_used_bits = 0;
   this.add_domain(offset, domain, rights, unmapped);

   this.atomic = new(1);

   this.Xis_busyX = 0;
   this.Xis_locked_by_fieldX = 1'b0;
   // Initialize Register ID
   this.reg_id = ++this.reg_id_factory;
   all_regs[this.reg_id] = this;
endfunction: new


function void vmm_ral_reg::Xlock_modelX();
   int idx;
   string fullname;

   if (this.locked) return;

   this.locked = 1;

endfunction: Xlock_modelX


function void vmm_ral_reg::add_domain(bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                      string                        domain,
                                      bit [1:0]                     rights,
                                      bit                           unmapped = 0);
   // Verify that this is a valid domain in the block
   string domains[];
   vmm_ral::access_e acc;
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add domain to locked register model");
      return;
   end

   case (rights)
     2'b11: acc = vmm_ral::RW;
     2'b10: acc = vmm_ral::RO;
     2'b01: acc = vmm_ral::WO;
     default:
       `vmm_error(this.log,
                  $psprintf("Register \"%s\" has no access rights in domain \"%s\"",
                            this.get_name(), domain));
   endcase

   parent.get_domains(domains);
   foreach(domains[i]) begin
      if (domains[i] == domain) begin
         automatic int n = this.offset_in_block.size();
   
         this.offset_in_block = new [n + 1] (this.offset_in_block);
         this.offset_in_block[n] = (unmapped) ? 'x : offset;
    
         this.domains = new [n + 1] (this.domains);
         this.domains[n] = domain;

         this.rights = new [n + 1] (this.rights);
         this.rights[n] = acc;

         this.frontdoor = new [n + 1] (this.frontdoor);
         this.frontdoor[n] = null;

         this.domain_coverage(domain, rights, n);
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in parent block %s of register \"%s\"",
                                  domain, parent.get_name(), this.get_name()));
endfunction: add_domain


function void vmm_ral_reg::register_field(vmm_ral_field field);
   int offset;
   int idx;
   
   if (this.locked) begin
      `vmm_error(this.log, "Cannot add field to locked register model");
      return;
   end

   if (field == null) `vmm_fatal(this.log, "Attempting to register NULL field");

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
      `vmm_error(this.log, $psprintf("Fields use more bits (%0d) than available in register \"%s\" (%0d)",
                                     this.n_used_bits, this.get_name(), this.n_bits));
   end

   // Check if there are overlapping fields
   if (idx > 0) begin
      if (this.fields[idx-1].get_lsb_pos_in_register() +
          this.fields[idx-1].get_n_bits() > offset) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in register \"%s\"",
                                        this.fields[idx-1].get_name(),
                                        field.get_name(), this.get_name()));
      end
   end
   if (idx < this.fields.size()-1) begin
      if (offset + field.get_n_bits() >
          this.fields[idx+1].get_lsb_pos_in_register()) begin
         `vmm_error(this.log, $psprintf("Field %s overlaps field %s in register \"%s\"",
                                        field.get_name(),
                                        this.fields[idx+1].get_name(),

                                      this.get_name()));
      end
   end
endfunction: register_field


function void vmm_ral_reg::Xregister_ral_accessX(vmm_ral_access access);
   // There can only be one RAL Access on a RAL model
   if (this.ral_access != null && this.ral_access != access) begin
      `vmm_fatal(this.log, $psprintf("Register \"%s\" is already used by another RAL access instance", this.get_name()));
   end
   this.ral_access = access;
   begin
     vmm_ral_field  fields[];
      
     this.get_fields(fields);
     foreach (fields[i]) begin
       fields[i].Xregister_ral_accessX(access);
     end
   end
endfunction: Xregister_ral_accessX


function void vmm_ral_reg::Xadd_constraintsX(string name);
   int n;

   if (this.locked) begin
      `vmm_error(this.log, "Cannot add constraints to locked register model");
      return;
   end

   // Check if the constraint block already exists
   foreach (this.constr[i]) begin
      if (this.constr[i] == name) begin
         `vmm_warning(this.log, $psprintf("Constraint \"%s\" already added",
                                          name));
         return;
      end
   end

   // Append the constraint name to the list
   n = this.constr.size();
   this.constr = new [n+1] (this.constr);
   this.constr[n] = name;
endfunction: Xadd_constraintsX


task vmm_ral_reg::XatomicX(bit on);
   if (on) this.atomic.get(1);
   else begin
      // Maybe a key was put back in by a spurious call to reset()
      void'(this.atomic.try_get(1));
      this.atomic.put(1);
   end
endtask: XatomicX


function string vmm_ral_reg::get_name();
   get_name = this.name;
endfunction: get_name


function string vmm_ral_reg::get_fullname();
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


function int vmm_ral_reg::get_n_domains();
   get_n_domains = this.domains.size();
endfunction: get_n_domains


function vmm_ral_block vmm_ral_reg::get_parent();
`ifndef VMM_12_UNDERPIN_VMM_RAL
   get_parent = this.parent;
`else
   begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      get_parent = parent;
   end
`endif
endfunction: get_parent


function void vmm_ral_reg::get_domains(ref string domains[]);
   domains = new [this.domains.size()] (this.domains);
endfunction: get_domains


function vmm_ral::access_e vmm_ral_reg::get_rights(string domain = "");
   int i;

   // No right restrictions if not shared
   if (this.domains.size() == 1) begin
      return vmm_ral::RW;
   end

   i = this.get_domain_index(domain);
   if (i < 0) return vmm_ral::RW;

   get_rights = this.rights[i];
endfunction: get_rights


function vmm_ral_block vmm_ral_reg::get_block();
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


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_reg::get_offset_in_block(string domain = "");
   foreach (this.domains[i]) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            `vmm_warning(this.log, $psprintf("Register \"%s\" is unmapped in domain \"%s\".", this.get_name(), domain));
            return '0;
         end
         
         return this.offset_in_block[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to find offset within domain \"%s\" in register \"%s\".",
                                    domain, this.get_name()));
   get_offset_in_block = '1;
endfunction: get_offset_in_block


function bit [`VMM_RAL_ADDR_WIDTH-1:0] vmm_ral_reg::get_address_in_system(string domain = "");
   bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
         
   int i = this.get_domain_index(domain);
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   if (i < 0) return 0;

   if (this.ral_access == null) begin
      `vmm_fatal(parent.log,
                 "RAL model is not associated with an access transactor");
      return 0;
   end
         
   if (this.offset_in_block[i] === 'x) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" is unmapped in domain \"%s\".", this.get_name(), this.domains[i]));
      return '1;
   end
         
   void'(this.ral_access.Xget_physical_addressesX(this.offset_in_block[i],
                                                  0, this.get_n_bytes(),
                                                  parent, this.domains[i], -1,
                                                  addr));

   get_address_in_system = addr[addr.size()-1];

   // Make sure to return the lower address as Xget_physical_addressesX()
   // returns the address in little-endian sequence.
   foreach (addr[i]) begin
      if (addr[i] < get_address_in_system) get_address_in_system = addr[i];
   end
endfunction: get_address_in_system


function int unsigned vmm_ral_reg::get_n_bytes();
   get_n_bytes = ((this.n_bits-1) / 8) + 1;
endfunction: get_n_bytes


function void vmm_ral_reg::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function void vmm_ral_reg::display_domain(string prefix = "",
                                          string domain = "");
   $write("%s\n", this.psdisplay_domain(prefix,domain));
endfunction: display_domain


function string vmm_ral_reg::psdisplay(string prefix = "");
   return this.psdisplay_domain(prefix);
endfunction: psdisplay

function string vmm_ral_reg::psdisplay_domain(string prefix = "",
                                              string domain = "");
   string res_str = "";
   string t_str = "";
   bit with_debug_info = 1'b0;

   $sformat(psdisplay_domain, "%sRegister %s -- %0d bytes @", prefix,
            this.get_fullname(), this.get_n_bytes());
   foreach (this.domains[i]) begin
      if (this.domains[i] == domain) begin
         if (this.offset_in_block[i] === 'x) begin
            psdisplay_domain = {psdisplay_domain, "none"};
         end
         else begin
            $sformat(psdisplay_domain, "%s'h%h", psdisplay_domain,
                     this.get_address_in_system(domain));
         end
         break;
      end
   end
   if (this.attributes.num() > 0) begin
      string name;
      void'(this.attributes.first(name));
      psdisplay_domain = {psdisplay_domain, "\n", prefix, "Attributes:"};
      do begin
         $sformat(psdisplay_domain, " %s=\"%s\"", name, this.attributes[name]);
      end while (this.attributes.next(name));
   end
   foreach(this.fields[i]) begin
      $sformat(psdisplay_domain, "%s\n%s", psdisplay_domain,
               this.fields[i].psdisplay({prefix, "   "}));
   end

   if (read_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay_domain = {psdisplay_domain, "\n", res_str, "currently executing read method"}; 
   end
   if ( write_in_progress == 1'b1) begin
      if (fname != "" && lineno != 0)
         $sformat(res_str, "%s:%0d ",fname, lineno);
      psdisplay_domain = {psdisplay_domain, "\n", res_str, "currently executing write method"}; 
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


function void vmm_ral_reg::get_fields(ref vmm_ral_field fields[]);
   fields = new [this.fields.size()];
   foreach(this.fields[i]) begin
      fields[i] = this.fields[i];
   end
endfunction: get_fields


function vmm_ral_field vmm_ral_reg::get_field_by_name(string name);
   foreach (this.fields[i]) begin
      if (this.fields[i].get_name() == name) begin
         return this.fields[i];
      end
   end
   `vmm_warning(this.log, $psprintf("Unable to locate field \"%s\" in register \"%s\".",
                                    name, this.get_name()));
   get_field_by_name = null;
endfunction: get_field_by_name


function void vmm_ral_reg::get_constraints(ref string names[]);
   names = new [this.constr.size()] (this.constr);
endfunction: get_constraints


function void vmm_ral_reg::set_attribute(string name,
                                         string value);
   if (name == "") begin
      `vmm_error(this.log, $psprintf("Cannot set anonymous attribute \"\" in register \"%s\". Please specify an attribute name.",
                                       name, this.get_fullname()));
      return;
   end

   if (this.attributes.exists(name)) begin
      if (value != "") begin
         `vmm_warning(this.log, $psprintf("Redefining attributed \"%s\" in register \"%s\" to \"%s\".",
                                          name, this.get_fullname(), value));
         this.attributes[name] = value;
      end
      else begin
         this.attributes.delete(name);
      end
      return;
   end

   if (value == "") begin
      `vmm_warning(this.log, $psprintf("Attempting to delete non-existent attribute \"%s\" in register \"%s\".",
                                       name, this.get_fullname()));
      return;
   end

   this.attributes[name] = value;
endfunction: set_attribute


function string vmm_ral_reg::get_attribute(string name,
                                           bit inherited = 1);
   if (this.attributes.exists(name)) begin
      return this.attributes[name];
   end

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (inherited) return this.parent.get_attribute(name);
`else
   if (inherited) begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      return parent.get_attribute(name);
   end
`endif

   return "";
endfunction: get_attribute


function void vmm_ral_reg::get_all_attributes(ref string names[],
                                              input bit inherited = 1);
   string tmp[];
   string name;
   bit    ok;
   int    i;

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (inherited) this.parent.get_all_attributes(tmp);
`else
   if (inherited) begin
      vmm_ral_block parent;
      $cast(parent, this._parent);
      parent.get_all_attributes(tmp); 
   end
`endif

   i = tmp.size();
   tmp = new [tmp.size() + this.attributes.num()] (tmp);

   ok = this.attributes.first(name);
   while (ok) begin
      int found = 0;
      foreach (tmp[j]) begin
         if (tmp[j] == name) begin
            found = 1;
            break;
         end
      end
      if (!found) tmp[i++] = name;
      ok = this.attributes.next(name);
   end
   names = new [i] (tmp);
endfunction: get_all_attributes


function bit vmm_ral_reg::can_cover(int models);
   return ((this.has_cover & models) == models);
endfunction: can_cover


function int vmm_ral_reg::set_cover(int is_on);
   if (is_on == vmm_ral::NO_COVERAGE) begin
      this.cover_on = is_on;
      return this.cover_on;
   end

   if ((this.has_cover & is_on) == 0) begin
      `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON any coverage because the corresponding coverage model was not generated.", this.get_fullname()));
      return this.cover_on;
   end

   if (is_on & vmm_ral::REG_BITS) begin
      if (this.has_cover & vmm_ral::REG_BITS) begin
          this.cover_on |= vmm_ral::REG_BITS;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Register Bit coverage because the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::FIELD_VALS) begin
      if (this.has_cover & vmm_ral::FIELD_VALS) begin
          this.cover_on |= vmm_ral::FIELD_VALS;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Field Value coverage because the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   if (is_on & vmm_ral::ADDR_MAP) begin
      if (this.has_cover & vmm_ral::ADDR_MAP) begin
          this.cover_on |= vmm_ral::ADDR_MAP;
      end else begin
          `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot turn ON Address Map coverage because the corresponding coverage model was not generated.", this.get_fullname()));
      end
   end

   set_cover = this.cover_on;
endfunction: set_cover


function bit vmm_ral_reg::is_cover_on(int is_on);
   if (this.can_cover(is_on) == 0) return 0;
   return ((this.cover_on & is_on) == is_on);
endfunction: is_cover_on


function void vmm_ral_reg::XforceX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                   vmm_ral::path_e               path,
                                   string                        domain);
   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      this.fields[i].XforceX(value >> this.fields[i].get_lsb_pos_in_register(),
                             path, domain);
   end
endfunction: XforceX


function void vmm_ral_reg::XwroteX(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                   vmm_ral::path_e               path,
                                   string                        domain);
   int j, w;

   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      j = this.fields[i].get_lsb_pos_in_register();
      w = this.fields[i].get_n_bits();
      this.fields[i].XwroteX((value >> j) & ((1 << w) - 1), path, domain);
   end
endfunction: XwroteX


function void vmm_ral_reg::set(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                               string                        fname = "",
                               int                           lineno = 0);
   // Split the value into the individual fields
   int j, w;
   this.fname = fname;
   this.lineno = lineno;

   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      j = this.fields[i].get_lsb_pos_in_register();
      w = this.fields[i].get_n_bits();
      this.fields[i].set((value >> j) & ((1 << w) - 1));
   end
endfunction: set


function bit vmm_ral_reg::predict(bit [`VMM_RAL_DATA_WIDTH-1:0] value,
                                  string                        fname = "",
                                  int                           lineno = 0, 
                                  bit                           force_predict = 0);
   this.fname = fname;
   this.lineno = lineno;
   if (this.Xis_busyX && !force_predict) begin
      `vmm_warning(this.log, $psprintf("Trying to predict value of register \"%s\" while it is being accessed",
                                       this.get_fullname()));
      return 0;
   end
   
   predict = 1;
   
   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      predict &= this.fields[i].predict(value >> this.fields[i].get_lsb_pos_in_register(),
                                        fname, lineno, force_predict);
   end
endfunction: predict


function bit[`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_reg::get(string  fname = "",
                                                       int     lineno = 0);
   // Concatenate the value of the individual fields
   // to form the register value
   int j, w;
   this.fname = fname;
   this.lineno = lineno;

   get = 0;
   
   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      j = this.fields[i].get_lsb_pos_in_register();
      get |= this.fields[i].get() << j;
   end
endfunction: get


function logic [`VMM_RAL_DATA_WIDTH-1:0]
   vmm_ral_reg::get_reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   // Concatenate the value of the individual fields
   // to form the register value
   int j, w;

   get_reset = 0;
   
   // Fields are stored in LSB or MSB order
   foreach (this.fields[i]) begin
      j = this.fields[i].get_lsb_pos_in_register();
      get_reset |= this.fields[i].get_reset(kind) << j;
   end
endfunction: get_reset


function void vmm_ral_reg::reset(vmm_ral::reset_e kind = vmm_ral::HARD);
   foreach (this.fields[i]) begin
      this.fields[i].reset(kind);
   end
   // Put back a key in the semaphore if it is checked out
   // in case a thread was killed during an operation
   void'(this.atomic.try_get(1));
   this.atomic.put(1);
endfunction: reset


function bit vmm_ral_reg::needs_update();
   needs_update = 0;
   foreach (this.fields[i]) begin
      if (this.fields[i].needs_update()) begin
         return 1;
      end
   end
endfunction: needs_update


task vmm_ral_reg::update(output vmm_rw::status_e status,
                         input  vmm_ral::path_e  path = vmm_ral::DEFAULT,
                         input  string           domain = "");
   bit [`VMM_RAL_DATA_WIDTH-1:0] upd, k;
   int j;

`ifndef VMM_12_UNDERPIN_VMM_RAL
   if (this.parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end
`else
   vmm_ral_block parent;
   $cast(parent, this._parent);
   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end
`endif

   status = vmm_rw::IS_OK;
   if (!this.needs_update()) return;

   this.XatomicX(1);

   // Concatenate the write-to-update values from each field
   // Fields are stored in LSB or MSB order
   upd = 0;
   foreach (this.fields[i]) begin
      j = this.fields[i].get_lsb_pos_in_register();
      k = (1 << this.fields[i].get_n_bits()) - 1;
      upd |= (this.fields[i].XupdX() & k) << j;
   end

   this.XwriteX(status, upd, path, domain, -1, -1, -1);

   this.XatomicX(0);
endtask: update


task vmm_ral_reg::write(output vmm_rw::status_e             status,
                        input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                        input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                        input  string                       domain = "",
                        input  int                          data_id = -1,
                        input  int                          scenario_id = -1,
                        input  int                          stream_id = -1,
                        input  string                       fname = "",
                        input  int                          lineno = 0);

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;
   this.write_in_progress = 1'b1;

   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   this.XatomicX(1);
   this.XwriteX(status, value, path, domain, data_id, scenario_id, stream_id, fname, lineno);
   this.XatomicX(0);
   this.fname = "";
   this.lineno = 0;
   this.write_in_progress = 1'b0;
endtask: write


task vmm_ral_reg::XwriteX(output vmm_rw::status_e             status,
                          input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                          input  vmm_ral::path_e              path,
                          input  string                       domain,
                          input  int                          data_id,
                          input  int                          scenario_id,
                          input  int                          stream_id,
                          input  string                       fname = "",
                          input  int                          lineno = 0);

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" not associated with RAL access object", this.get_name()));
      return;
   end
   
   if (path == vmm_ral::DEFAULT) path = parent.get_default_access();

   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         foreach (f.XcbsX[j]) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.pre_write(f, tmp, path, domain);
         end

         value = (value & ~msk) | (tmp << lsb);
      end
   end
   `vmm_callback(vmm_ral_reg_callbacks,
              pre_write(this, value, path, domain));

   if (path == vmm_ral::DEFAULT) path = parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for register \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         this.Xis_busyX = 1;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].fname = fname;
            this.frontdoor[di].lineno = lineno;
            this.frontdoor[di].write(status, value,
                                     data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;

            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Register \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end

            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         0, this.get_n_bytes(),
                                                         parent,
                                                         this.domains[di], -1,
                                                         addr);
            j = 0;
            n_bits = this.get_n_bytes() * 8;
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               data = value >> (j*8);
               this.ral_access.write(status, addr[i], data,
                                     (n_bits > w*8) ? w*8 : n_bits,
                                     parent.get_external_domain(this.domains[di]),
                                     data_id, scenario_id, stream_id, fname, lineno);
               if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) return;
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) begin
            this.sample(value, 0, di);
            parent.XsampleX(this.offset_in_block[di], di, 0);
         end

         this.Xis_busyX = 0;

         this.XwroteX(value, path, domain);
      end
      
      vmm_ral::BACKDOOR: begin
         bit [`VMM_RAL_DATA_WIDTH-1:0] reg_val;
         bit [`VMM_RAL_DATA_WIDTH-1:0] final_val;

         // Mimick the final value after a physical read
         this.backdoor.read(status, reg_val,
                            data_id, scenario_id, stream_id);
         if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) return;

         begin
            int j, w;

            // Fields are stored in LSB or MSB order
            final_val = '0;
            foreach (this.fields[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] field_val;
               j = this.fields[i].get_lsb_pos_in_register();
               w = this.fields[i].get_n_bits();
               field_val = this.fields[i].XpredictX((reg_val >> j) & ((1 << w) - 1),
                                                    (value >> j) & ((1 << w) - 1),
                                                    domain);
               final_val |= field_val << j;
            end
         end
         this.backdoor.write(status, final_val, data_id, scenario_id, stream_id);
         this.XwroteX(final_val, path, "-");
      end
   endcase

   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      value = this.get();

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         foreach (f.XcbsX[j]) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.post_write(f, tmp, path, domain, status);
         end
      end
   end

   `vmm_trace(this.log, $psprintf("Wrote register \"%s\" via %s with: 'h%h",
                                  this.get_fullname(),
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   `vmm_callback(vmm_ral_reg_callbacks,
                 post_write(this, value, path, domain, status));
endtask: XwriteX


task vmm_ral_reg::read(output vmm_rw::status_e             status,
                       output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  vmm_ral::path_e              path = vmm_ral::DEFAULT,
                       input  string                       domain = "",
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1,
                       input  string                       fname = "",
                       input  int                          lineno = 0);
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;
   this.read_in_progress = 1'b1;
   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   this.XatomicX(1);
   this.XreadX(status, value, path, domain, data_id, scenario_id, stream_id, fname, lineno);
   this.XatomicX(0);
   this.fname = "";
   this.lineno = 0;
   this.read_in_progress = 1'b0;
endtask: read


task vmm_ral_reg::XreadX(output vmm_rw::status_e             status,
                         output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                         input  vmm_ral::path_e              path,
                         input  string                       domain,
                         input  int                          data_id,
                         input  int                          scenario_id,
                         input  int                          stream_id,
                         input  string                       fname = "",
                         input  int                          lineno = 0);
`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   status = vmm_rw::ERROR;
   
   if (this.ral_access == null) begin
      `vmm_error(this.log, $psprintf("Register \"%s\" not associated with RAL access object", this.get_name()));
      return;
   end
   
   if (path == vmm_ral::DEFAULT) path = parent.get_default_access();

   foreach (fields[i]) begin
      vmm_ral_field f = fields[i];

      foreach (f.XcbsX[j]) begin
         vmm_ral_field_callbacks cb;
         if (!$cast(cb, f.XcbsX[j])) continue;
         cb.pre_read(f, path, domain);
      end
   end
   `vmm_callback(vmm_ral_reg_callbacks,
                 pre_read(this, path, domain));

   if (path == vmm_ral::DEFAULT) path = parent.get_default_access();

   if (path == vmm_ral::BACKDOOR &&
       this.backdoor == null) begin
      `vmm_warning(this.log, $psprintf("No backdoor access available for register \"%s\". Using frontdoor instead.", this.get_name()));
      path = vmm_ral::BFM;
   end

   case (path)
      
      vmm_ral::BFM: begin
         int di = this.get_domain_index(domain);
         if (di < 0) return;
         
         this.Xis_busyX = 1;

         if (this.frontdoor[di] != null) begin
            this.frontdoor[di].fname = fname;
            this.frontdoor[di].lineno = lineno;
            this.frontdoor[di].read(status, value,
                                   data_id, scenario_id, stream_id);
         end
         else begin
            bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[];
            int w, j;
            int n_bits;
         
            if (this.offset_in_block[di] === 'x) begin
               `vmm_error(this.log, $psprintf("Register \"%s\" unmapped in domain \"%s\" does not have a user-defined frontdoor",
                                              this.get_name(),
                                              this.domains[di]));
               return;
            end
         
            w = this.ral_access.Xget_physical_addressesX(this.offset_in_block[di],
                                                         0, this.get_n_bytes(),
                                                         parent,
                                                         this.domains[di], -1, 
                                                         addr);
            j = 0;
            n_bits = this.get_n_bytes() * 8;
            value = 0;
            foreach (addr[i]) begin
               bit [`VMM_RAL_DATA_WIDTH-1:0] data;
               this.ral_access.read(status, addr[i], data,
                                    (n_bits > w*8) ? w*8 : n_bits,
                                    parent.get_external_domain(this.domains[di]),
                                    data_id, scenario_id, stream_id, fname, lineno);
               if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) return;
               value |= (data & ((1 << (w*8)) - 1)) << (j*8);
               j += w;
               n_bits -= w * 8;
            end
         end

         if (this.cover_on) begin
            this.sample(value, 1, di);
            parent.XsampleX(this.offset_in_block[di], di, 1);
         end

         this.Xis_busyX = 0;

         this.XforceX(value, path, domain);
      end
      
      vmm_ral::BACKDOOR: begin
         bit [`VMM_RAL_DATA_WIDTH-1:0] final_val;

         this.backdoor.read(status, value, data_id, scenario_id, stream_id);
         final_val = value;

         // Need to clear RC fields and mask WO fields
         if (status == vmm_rw::IS_OK || status == vmm_rw::HAS_X) begin
            bit [`VMM_RAL_DATA_WIDTH-1:0] wo_mask = 0;

            foreach (this.fields[i]) begin
               vmm_ral::access_e acc = this.fields[i].get_access("BaCkDoOr");
               if (acc == vmm_ral::RC) begin
                  final_val &= ~(((1<<this.fields[i].get_n_bits())-1) << this.fields[i].get_lsb_pos_in_register());
               end
               else if (acc == vmm_ral::WO) begin
                  wo_mask |= ((1<<this.fields[i].get_n_bits())-1) << this.fields[i].get_lsb_pos_in_register();
               end
            end

            if (final_val != value) begin
               this.backdoor.write(status, final_val,
                                   data_id, scenario_id, stream_id);
            end

            value &= ~wo_mask;
            this.XforceX(final_val, path, "-");
         end
      end
   endcase


   begin
      bit [`VMM_RAL_DATA_WIDTH-1:0] tmp;
      bit [`VMM_RAL_DATA_WIDTH-1:0] msk;
      int lsb;

      foreach (fields[i]) begin
         vmm_ral_field f = fields[i];

         lsb = f.get_lsb_pos_in_register();

         msk = ((1<<f.get_n_bits())-1) << lsb;
         tmp = (value & msk) >> lsb;

         foreach (f.XcbsX[j]) begin
            vmm_ral_field_callbacks cb;
            if (!$cast(cb, f.XcbsX[j])) continue;
            cb.post_read(f, tmp, path, domain, status);
         end

         value = (value & ~msk) | (tmp << lsb);
      end
   end

   `vmm_trace(this.log, $psprintf("Read register \"%s\" via %s: 'h%h",
                                  this.get_fullname(),
                                  (path == vmm_ral::BFM) ? "frontdoor" : "backdoor",
                                  value));

   `vmm_callback(vmm_ral_reg_callbacks,
                 post_read(this, value, path, domain, status));
endtask: XreadX


task vmm_ral_reg::poke(output vmm_rw::status_e             status,
                       input  bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1,
                       input  string                       fname = "",
                       input  int                          lineno = 0);

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;
   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(1);

   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available to poke register \"%s\"", this.get_name()));
      status = vmm_rw::ERROR;
      if(!this.Xis_locked_by_fieldX)
        this.XatomicX(0);
      return;
   end

   this.backdoor.write(status, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Poked register \"%s\" with: 'h%h",
                                  this.get_fullname(), value));

   this.XforceX(value, vmm_ral::BACKDOOR, "-");
   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(0);
   this.fname = "";
   this.lineno = 0;
endtask: poke


task vmm_ral_reg::peek(output vmm_rw::status_e             status,
                       output bit[`VMM_RAL_DATA_WIDTH-1:0] value,
                       input  int                          data_id = -1,
                       input  int                          scenario_id = -1,
                       input  int                          stream_id = -1,
                       input  string                       fname = "",
                       input  int                          lineno = 0);

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;
   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(1);
   if (this.backdoor == null) begin
      `vmm_error(this.log, $psprintf("No backdoor access available peek register \"%s\"", this.get_name()));
      status = vmm_rw::ERROR;
      if(!this.Xis_locked_by_fieldX)
        this.XatomicX(0);
      return;
   end
   this.backdoor.read(status, value, data_id, scenario_id, stream_id);

   `vmm_trace(this.log, $psprintf("Peeked register \"%s\": 'h%h",
                                  this.get_fullname(), value));

   this.XforceX(value, vmm_ral::BACKDOOR, "-");

   if(!this.Xis_locked_by_fieldX)
     this.XatomicX(0);
   this.fname = "";
   this.lineno = 0;
endtask: peek


task vmm_ral_reg::mirror(output vmm_rw::status_e  status,
                         input  vmm_ral::check_e  check = vmm_ral::QUIET,
                         input  vmm_ral::path_e   path = vmm_ral::DEFAULT,
                         input  string            domain = "",
                         input  string            fname = "",
                         input  int               lineno = 0);
   bit [`VMM_RAL_DATA_WIDTH-1:0] v;
   bit [`VMM_RAL_DATA_WIDTH-1:0] exp;

`ifdef VMM_12_UNDERPIN_VMM_RAL
   vmm_ral_block parent;
   $cast(parent, this._parent);
`endif

   this.fname = fname;
   this.lineno = lineno;

   if (parent.Xis_powered_downX) begin
      `vmm_error(this.log, $psprintf("Register %s cannot be accessed when its parent block is powered down", this.get_fullname()));
      return;
   end

   if (path == vmm_ral::DEFAULT) path = parent.get_default_access();

   this.XatomicX(1);

   if (path == vmm_ral::BACKDOOR && this.backdoor != null) begin
      domain = "BaCkDoOr";
   end

   // Remember what we think the value is before it gets updated
   if (check == vmm_ral::VERB) begin
      exp = this.get();
      // Any WO field will readback as 0's
      foreach(this.fields[i]) begin
         if (this.fields[i].get_access(domain) == vmm_ral::WO) begin
            exp &= ~(((1 << this.fields[i].get_n_bits())-1)
                     << this.fields[i].get_lsb_pos_in_register());
         end
      end
   end

   this.XreadX(status, v, path, domain, -1, -1, -1, fname, lineno);

   if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) begin
     if($test$plusargs("ral_concurrent_backdoor_mirror")) begin
       if(path!=vmm_ral::BACKDOOR)
         this.XatomicX(0);
     end
     else
       this.XatomicX(0);

      return;
   end

   if (check == vmm_ral::VERB) begin
      // Check that our idea of the register value matches
      // what we just read from the DUT, minus the don't care fields
      bit [`VMM_RAL_DATA_WIDTH-1:0] dc = 0;

      foreach(this.fields[i]) begin
         vmm_ral::access_e acc = this.fields[i].get_access(domain);
         if (acc == vmm_ral::DC) begin
            dc |= ((1 << this.fields[i].get_n_bits())-1)
                  << this.fields[i].get_lsb_pos_in_register();
         end
         else if (acc == vmm_ral::WO) begin
            // WO fields will always read-back as 0
            exp &= ~(((1 << this.fields[i].get_n_bits())-1)
                     << this.fields[i].get_lsb_pos_in_register());
         end
      end

      if ((v|dc) !== (exp|dc)) begin
         `vmm_error(this.log, $psprintf("Register \"%s\" value read from DUT (0x%h) does not match mirrored value (0x%h)",
                                        this.get_name(), v, (exp ^ ('x & dc))));
      end
   end

   this.XatomicX(0);
   this.fname = "";
   this.lineno = 0;

   if(status == vmm_rw::HAS_X)
     status = vmm_rw::IS_OK;
endtask: mirror


function void vmm_ral_reg::set_frontdoor(vmm_ral_reg_frontdoor ftdr,
                                         string                domain = "",
                                         string                fname = "",
                                         int                   lineno = 0);
   this.fname = fname;
   this.lineno = lineno;
   foreach(this.domains[i]) begin
      if (this.domains[i] == domain) begin
         this.frontdoor[i] = ftdr;
         return;
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in register %s", domain, this.get_fullname()));
endfunction: set_frontdoor


function vmm_ral_reg_frontdoor vmm_ral_reg::get_frontdoor(string domain = "");
   foreach(this.domains[i]) begin
      if (this.domains[i] == domain) begin
         return this.frontdoor[i];
      end
   end
   `vmm_error(this.log, $psprintf("Domain \"%s\" not found in register %s", domain, this.get_fullname()));
endfunction: get_frontdoor


function void vmm_ral_reg::set_backdoor(vmm_ral_reg_backdoor bkdr,
                                        string               fname = "",
                                        int                  lineno = 0);
   this.fname = fname;
   this.lineno = lineno;
   if (this.backdoor != null) this.backdoor.kill_update_thread();
   this.backdoor = bkdr;
endfunction: set_backdoor


function vmm_ral_reg_backdoor vmm_ral_reg::get_backdoor();
   get_backdoor = this.backdoor;
endfunction: get_backdoor


function void vmm_ral_reg::prepend_callback(vmm_ral_reg_callbacks cb,
                                            string                fname = "",
                                            int                   lineno = 0);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with register \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Prepend new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_ral_reg::append_callback(vmm_ral_reg_callbacks cb,
                                           string                fname = "",
                                           int                   lineno = 0);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, $psprintf("Callback has already been registered with register \"%s\"", this.get_name()));
         return;
      end
   end
   
   // Append new callback
   cb.fname = fname;
   cb.lineno = lineno;
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_ral_reg::unregister_callback(vmm_ral_reg_callbacks cb);
   foreach (this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         int j = i;
         // Unregister it
         this.callbacks.delete(j);
         return;
      end
   end

   `vmm_warning(this.log, $psprintf("Callback was not registered with register \"%s\"", this.get_name()));
endfunction: unregister_callback


function int vmm_ral_reg::get_domain_index(string domain);
   // If the domain is "" and there is only one domain,
   // assume it is the one domain available to avoid
   // having to always have to specify domains
   if (domain == "" && this.domains.size() == 1) return 0;

   foreach (this.domains[i]) begin
      if (this.domains[i] == domain) return i;
   end
   `vmm_warning(this.log, $psprintf("Unknown domain name \"%s\" in register \"%s\".", domain, this.get_name()));
   return -1;
endfunction: get_domain_index


task vmm_ral_reg_frontdoor::write(output vmm_rw::status_e              status,
                                  input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_reg_frontdoor::write() method has not been overloaded");
endtask: write


task vmm_ral_reg_frontdoor::read(output vmm_rw::status_e              status,
                                 output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);
   `vmm_fatal(this.log, "vmm_ral_reg_frontdoor::read() method has not been overloaded");
endtask: read


function void vmm_ral_reg::sample(bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  bit                           is_read,
                                  int                           domain);
   // Nothing to do in this base class
endfunction


function int unsigned vmm_ral_reg::get_reg_ID();
   get_reg_ID =  this.reg_id;
endfunction

function vmm_ral_reg vmm_ral_get_reg_by_ID(int unsigned id);
   vmm_ral_reg rg;
   if (rg.all_regs.exists(id)) 
      vmm_ral_get_reg_by_ID = rg.all_regs[id];
   else vmm_ral_get_reg_by_ID = null;
endfunction

function void vmm_ral_reg::sample_field_values();
   `vmm_warning(this.log, $psprintf("Register \"%s\" - Cannot sample field values because the corresponding coverage model was not generated for this register.", this.get_fullname()));
endfunction
