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
// CLASS: vmm_ral_access
// RAL component managing accesses to registers and memories through physical interfaces.
// Also provides an access-by-address and access-by-name service to registers and memories.
// 
//------------------------------------------------------------------------------
class vmm_ral_access extends `VMM_XACTOR;
   vmm_ral::path_e default_path = vmm_ral::BFM;  // Cannot be "DEFAULT"

   protected vmm_ral_block_or_sys model;
   
   protected vmm_rw_xactor rw_exec[string]; // One per domain
   local string fname = "";
   local int    lineno = 0;

   local string dmn_name_sq[$];
   extern function new(`VMM_RAL_BASE_NEW_ARGS );
   extern protected virtual task main();
   extern protected task obs_update(string domain); /*local*/

   //------------------------------------------------------------------------------
   // FUNCTION: set_model
   // Associates the specified RAL abstraction model with the RAL physical access component
   // instance. Once a model is associated with an access component, registers, fields and
   // memories can be accessed through the RAL. A model can be associated with only one access
   // component. Similarly, an access component can be associated with only one abstraction
   // model. It is possible to have multiple instances of the access component associated
   // with their respective abstraction model. 
   //------------------------------------------------------------------------------
   extern function void set_model(vmm_ral_block_or_sys model);

   //------------------------------------------------------------------------------
   // FUNCTION: get_model
   // Return the RAL abstraction model that was associated with the RAL physical access component
   // instance using the <vmm_ral_access::set_model> method. 
   //------------------------------------------------------------------------------
   extern function vmm_ral_block_or_sys get_model();

   //------------------------------------------------------------------------------
   // FUNCTION: add_xactor
   // Associates the specified physical-level transactor with the specified domain in
   // the RAL abstraction model. The specified domain must exist in the model and only one
   // transactor can be associated with a particular domain. The physical-level transactor
   // is implicitly started when added to the RAL abstraction model. This allows the predefined
   // RAL tests to execute and the RAL model to later be used to configure the DUT in the <vmm_env::cfg_dut>
   // step, before the <vmm_env::start> step has been executed. The physical-level transactor
   // can be explicitly started in the <vmm_env::start> step without adverse effects. If
   // a domain has no physical-level transactor associated with it, it is not possible to
   // perform physical accesses to its registers and memories. 
   //------------------------------------------------------------------------------
   extern function void add_xactor(vmm_rw_xactor xact,
                                   string        domain = "");


   //------------------------------------------------------------------------------
   // TASK: write
   // Writes the specified value at the specified physical address through the physical
   // interface of the specified domain. Returns an indication of the success or failure
   // of the operation.
   //------------------------------------------------------------------------------
   extern task write(output vmm_rw::status_e status,
                     input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                     input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                     input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                     input  string                        domain = "",
                     input  int                           data_id = -1,
                     input  int                           scenario_id = -1,
                     input  int                           stream_id = -1,
                     input  string                        fname = "",
                     input  int                           lineno = 0,
                     input  bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '1 );


   //------------------------------------------------------------------------------
   // TASK: read
   // Reads a value from the specified physical address through the physical interface of
   // the specified domain. Returns an indication of the success or failure of the operation.
   //------------------------------------------------------------------------------
   extern task read(output vmm_rw::status_e status,
                    input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                    output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                    input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                    input  string                        domain = "",
                    input  int                           data_id = -1,
                    input  int                           scenario_id = -1,
                    input  int                           stream_id = -1,
                    input  string                        fname = "",
                    input  int                           lineno = 0,
                    input  bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '1
                    );


   //------------------------------------------------------------------------------
   // TASK: burst_write
   // Writes a set of value using a burst write cycle through the physical interface of the
   // specified domain. The following parameters are used to populate the <vmm_rw_burst>
   // descriptor that will eventually be executed by the <vmm_rw_xactor::execute_burst>
   // method. 
   //------------------------------------------------------------------------------
   extern task burst_write(output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                           input  vmm_data                      user = null,
                           input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1,
                           input  string                        fname = "",
                           input  int                           lineno = 0
                    );


   //------------------------------------------------------------------------------
   // TASK: burst_read
   // Reads a set of values using a burst read cycle through the physical interface of the specified
   // domain. The following parameters are used to populate the <vmm_rw_burst> descriptor
   // that will eventually be executed by the <vmm_rw_xactor::execute_burst> method:
   // start incr max n_beats user Returns an indication of the success or failure of the operation.
   // The mirrored content of any register or memory located in the burst area is not updated.
   // This method is provided if low-level burst-read operations are necessary. Burst-read
   // operations should be done using the <vmm_ral_mem::burst_read> method. 
   //------------------------------------------------------------------------------
   extern task burst_read(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                          input  int                           n_beats,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                          input  vmm_data                      user = null,
                          input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1,
                          input  string                        fname = "",
                          input  int                           lineno = 0
                    );


   //------------------------------------------------------------------------------
   // FUNCTION: set_by_name
   // Locates the register with the specified name and sets its value mirrored in the RAL abstraction
   // model. The actual register in the design is not written or updated. See <vmm_ral_reg::set>
   // for more details on the operation of the mirror. See <vmm_ral_block::get_reg_by_name>
   // for details on how the register is located. 
   //
   // Returns TRUE if a unique register of the specified
   // name is found in the RAL model. 
   //
   // Returns FALSE otherwise. It is better to use the <vmm_ral_reg::set>
   // method directly in the RAL abstraction class for a register in the RAL model (accessed
   // using hierarchical references)
   // rather than using this method with a hard-coded name. 
   //------------------------------------------------------------------------------
   extern virtual function bit set_by_name(input string                        name,
                                           input bit [`VMM_RAL_DATA_WIDTH-1:0] value);

   //------------------------------------------------------------------------------
   // FUNCTION: get_by_name
   // Locates the register with the specified name and returns its value mirrored in the RAL
   // abstraction model. The actual register in the design is not read. See <vmm_ral_reg::get>
   // for more details on the operation of the mirror. See <vmm_ral_block::get_reg_by_name>
   // for details on how the register is located. 
   //
   // Returns TRUE if a unique register of the specified
   // name is found in the RAL model. 
   //
   // Returns FALSE otherwise. It is better to use the <vmm_ral_reg::get>
   // method directly in the RAL abstraction class for a register in the RAL model (accessed
   // using hierarchical references)
   // rather than using this method with a hard-coded name. 
   //------------------------------------------------------------------------------
   extern virtual function bit get_by_name(input  string                        name,
                                           output bit [`VMM_RAL_DATA_WIDTH-1:0] value);


   //------------------------------------------------------------------------------
   // TASK: write_by_name
   // Locates the register with the specified name and performs the specified write operation
   // through its RAL abstraction model. The mirror is updated. See <vmm_ral_block::get_reg_by_name>
   // for details on how the register is located. 
   //------------------------------------------------------------------------------
   extern task write_by_name(output vmm_rw::status_e              status,
                             input  string                        name,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                             input  string                        domain = "",
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1,
                             input  string                        fname = "",
                             input  int                           lineno = 0
                    );


   //------------------------------------------------------------------------------
   // TASK: read_by_name
   // Locates the register with the specified name and performs the specified read operation
   // through its RAL abstraction model. The mirror is updated. See <vmm_ral_block::get_reg_by_name>
   // for details on how the register is located. 
   //------------------------------------------------------------------------------
   extern task read_by_name(output vmm_rw::status_e              status,
                            input  string                        name,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                            input  string                        domain = "",
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1,
                            input  string                        fname = "",
                            input  int                           lineno = 0
                    );


   //------------------------------------------------------------------------------
   // TASK: write_mem_by_name
   // Locates the memory with the specified name and performs the specified write operation
   // through its RAL abstraction model. The mirror is updated. See <vmm_ral_block::get_mem_by_name>
   // for details on how the memory is located. 
   //------------------------------------------------------------------------------
   extern task write_mem_by_name(output vmm_rw::status_e              status,
                                 input  string                        name,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  vmm_ral::path_e               path   = vmm_ral::DEFAULT,
                                 input  string                        domain = "",
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1,
                                 input  string                        fname = "",
                                 input  int                           lineno = 0
                    );   


   //------------------------------------------------------------------------------
   // TASK: read_mem_by_name
   // Locates the memory with the specified name and performs the specified read operation
   // through its RAL abstraction model. The mirror is updated. See <vmm_ral_block::get_mem_by_name>
   // for details on how the memory is located. 
   //------------------------------------------------------------------------------
   extern task read_mem_by_name(output vmm_rw::status_e status,
                                input  string                        name,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                input  string                        domain = "",
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1,
                                input  string                        fname = "",
                                input  int                           lineno = 0
                    );

   /*local*/ extern function int
     Xget_physical_addressesX(bit [`VMM_RAL_ADDR_WIDTH-1:0]     base_addr,
                              bit [`VMM_RAL_ADDR_WIDTH-1:0]     mem_offset,
                              int unsigned                      n_bytes,
                              vmm_ral_block_or_sys              in_block,
                              string                            domain,
                              int                               n_used_bytes, // Number of bytes containing valid data.
                              ref bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[]);
					
     extern function bit Xsupports_byte_enableX( string        domain = "");

endclass: vmm_ral_access


function vmm_ral_access::new(`VMM_RAL_BASE_NEW_EXTERN_ARGS);

   super.new("VMM RAL Access", 
   `ifdef VMM_12_UNDERPIN_VMM_RAL
            name);
      `ifdef VMM_XACTOR_BASE
        super.set_parent_object(parent);
      `endif
   `else
      "Main");
   `endif
endfunction: new

task vmm_ral_access::main();
string domain_name;
fork
  super.main();
join_none		
fork
  while(1) begin
    wait(dmn_name_sq.size() > 0);
    domain_name = dmn_name_sq.pop_front();
    fork
      this.obs_update(domain_name);
    join_none
  end
join_none		
endtask

task vmm_ral_access::obs_update(string domain);
  vmm_rw_access tr;
  vmm_ral_reg rg;
		
  forever begin
    this.rw_exec[domain].obsv_chan.get(tr);
    rg = this.model.get_reg_by_offset(tr.addr);
    void'(rg.predict(tr.data));
  end
endtask

function void vmm_ral_access::set_model(vmm_ral_block_or_sys model);
   if (this.model != null) begin
      `vmm_error(this.log, "A RAL abstraction model has already been associated with this RAL access interface");
      return;
   end

   this.model = model;

   // Register this RAL access object with the RAL model
   model.Xregister_ral_accessX(this);
endfunction: set_model


function vmm_ral_block_or_sys vmm_ral_access::get_model();
   get_model = this.model;
endfunction: get_model


function void vmm_ral_access::add_xactor(vmm_rw_xactor xact,
                                         string        domain = "");
   if (this.model == null) begin
      `vmm_error(this.log, "A RAL abstraction model has not yet been associated with this RAL access interface");
      return;
   end

   if(xact == null) begin
      `vmm_error(this.log, "Null argument provided for RW Xactor");
      return;
   end

   // Check if the specified domain matches a domain in the model
   begin
      string domains[];
      bit found = 0;

      model.get_domains(domains);
      foreach (domains[i]) begin
         if (domains[i] == domain) begin
            found = 1;
            break;
         end
      end
      if (!found) begin
         `vmm_error(this.log, $psprintf("Domain \"%s\" does not exist in RAL model",
                                        domain));
         if (this.log.start_msg(vmm_log::FAILURE_TYP, vmm_log::ERROR_SEV)) begin
            string msg;
            void'(this.log.text($psprintf("Domain \"%s\" does not exist in RAL model \"%s\"",
                                          domain, this.model.get_name())));
            msg = "Available domains are:";
            foreach (domains[i]) begin
               $sformat(msg, "%s \"%s\"", msg, domains[i]);
            end
            void'(this.log.text(msg));
            this.log.end_msg();
         end
         return;
      end
   end

   if (this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("Transactor for domain \"%s\" already exists",
                                     domain));
   end
   else begin
      this.rw_exec[domain] = xact;

      // Make sure transactor is started
      xact.start_xactor();
      dmn_name_sq.push_back(domain); /*to fork of the update thread for observe_single */
   end
endfunction: add_xactor


task vmm_ral_access::write(output vmm_rw::status_e              status,
                           input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                           input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                           input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                           input  string                        domain = "",
                           input  int                           data_id = -1,
                           input  int                           scenario_id = -1,
                           input  int                           stream_id = -1,
                           input  string                        fname = "",
                           input  int                           lineno = 0,
																										 input  bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '1
                    );
   this.fname = fname;
   this.lineno = lineno;
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".\nPlease check if 'vmm_ral_access::add_xactor()' was called.\n",
                                     domain));
      return;
   end

   `vmm_trace(this.log, $psprintf("Writing 'h%h at 'h%h via domain \"%s\"...",
                                  data, addr, domain));

   begin
      vmm_rw_access rw = new(
`ifdef VMM_12_UNDERPIN_VMM_DATA
         , "w_access"
`endif
     );

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind = vmm_rw::WRITE;
      rw.addr = addr;
      rw.data = data;
      rw.n_bits = n_bits;
      rw.byte_enable = byte_en;
      this.rw_exec[domain].exec_chan.put(rw);
`ifndef VMM_DATA_NO_NOTIFY_ALL
      rw.notify.wait_for(vmm_data::ENDED);
`endif
      status = rw.status;
   end
endtask: write


task vmm_ral_access::read(output vmm_rw::status_e              status,
                          input  bit [`VMM_RAL_ADDR_WIDTH-1:0] addr,
                          output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                          input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                          input  string                        domain = "",
                          input  int                           data_id = -1,
                          input  int                           scenario_id = -1,
                          input  int                           stream_id = -1,
                          input  string                        fname = "",
                          input  int                           lineno = 0,
																										input  bit [`VMM_RW_BYTENABLE_WIDTH-1:0] byte_en = '1
                    );
   this.fname = fname;
   this.lineno = lineno;
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      //`vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".\nPlease check if 'vmm_ral_access::add_xactor()' was called.\n",
                                     domain));
      return;
   end

   begin
      vmm_rw_access rw = new
`ifdef VMM_12_UNDERPIN_VMM_DATA
         (, "w_access")
`endif
      ;

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind   = vmm_rw::READ;
      rw.addr   = addr;
      rw.n_bits = n_bits;
						rw.byte_enable = byte_en;
      this.rw_exec[domain].exec_chan.put(rw);
`ifdef VMM_RAL_PIPELINED_ACCESS
  `ifdef VMM_DATA_NO_NOTIFY_ALL
      `vmm_fatal(log, "You cannot turn off VMM Data notification with Pipelined RAL access");
  `else
      rw.notify.wait_for(vmm_data::ENDED);
  `endif
`else
  `ifndef VMM_DATA_NO_NOTIFY_ALL
      rw.notify.wait_for(vmm_data::ENDED);
  `endif
`endif
      data = rw.data;
      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Read 'h%h from 'h%h via domain \"%s\"...",
                                  data, addr, domain));

endtask: read


task vmm_ral_access::burst_write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                 input  vmm_data                      user = null,
                                 input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                                 input  string                        domain = "",
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1,
                                 input  string                        fname = "",
                                 input  int                           lineno = 0
                    );
   this.fname = fname;
   this.lineno = lineno;
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".\nPlease check if 'vmm_ral_access::add_xactor()' was called.\n",
      //`vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
                                     domain));
      return;
   end

   begin
      vmm_rw_burst rw = new
      `ifdef VMM_12_UNDERPIN_VMM_DATA
         (this, "write_burst");
	  `else	 
         ;
      `endif

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind      = vmm_rw::WRITE;
      rw.addr      = start;
      rw.incr_addr = incr;
      rw.max_addr  = max;
      rw.n_beats   = data.size();
      rw.n_bits    = n_bits;
      rw.user_data = user;

      rw.data = new [rw.n_beats];
      foreach (data[i]) rw.data[i] = data[i];

      this.rw_exec[domain].exec_chan.put(rw);
`ifndef VMM_DATA_NO_NOTIFY_ALL
      rw.notify.wait_for(vmm_data::ENDED);
`endif
      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Burst-wrote %0d data from ['h%h+'h%h %%'h%h] via domain \"%s\"...",
                                  data.size(), start, incr, max, domain));

endtask: burst_write


task vmm_ral_access::burst_read(output vmm_rw::status_e              status,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] start,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] incr,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] max,
                                input  int                           n_beats,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data[],
                                input  vmm_data                      user = null,
                                input  int                           n_bits = `VMM_RAL_DATA_WIDTH,
                                input  string                        domain = "",
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1,
                                input  string                        fname = "",
                                input  int                           lineno = 0
                    );
   this.fname = fname;
   this.lineno = lineno;
   status = vmm_rw::ERROR;
   
   if (!this.rw_exec.exists(domain)) begin
      //`vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".",
      `vmm_error(this.log, $psprintf("No transactor available to physically access domain \"%s\".\nPlease check if 'vmm_ral_access::add_xactor()' was called.\n",
                                     domain));
      return;
   end

   begin
      vmm_rw_burst rw = new
      `ifdef VMM_12_UNDERPIN_VMM_DATA
         (this, "read_burst");
	  `else	 
         ;
      `endif

      rw.data_id     = data_id;
      rw.scenario_id = scenario_id;
      rw.stream_id   = stream_id;

      rw.kind      = vmm_rw::READ;
      rw.addr      = start;
      rw.incr_addr = incr;
      rw.max_addr  = max;
      rw.n_beats   = n_beats;
      rw.n_bits    = n_bits;
      rw.user_data = user;

      this.rw_exec[domain].exec_chan.put(rw);
`ifdef VMM_RAL_PIPELINED_ACCESS
  `ifdef VMM_DATA_NO_NOTIFY_ALL
      `vmm_fatal(log, "You cannot turn of VMM Data notification with Pipelined RAL access");
  `else
      if (rw.status == vmm_rw::PENDING) begin
         rw.notify.wait_for(vmm_data::ENDED);
      end
  `endif
`else
  `ifndef VMM_DATA_NO_NOTIFY_ALL
      rw.notify.wait_for(vmm_data::ENDED);
  `endif
`endif
      data = new [rw.data.size()];
      foreach (data[i]) data[i] = rw.data[i];
      status = rw.status;
   end

   `vmm_trace(this.log, $psprintf("Burst-read %0d data from ['h%h+'h%h %%'h%h] via domain \"%s\"...",
                                  data.size(), start, incr, max, domain));

endtask: burst_read


function bit vmm_ral_access::set_by_name(string                        name,
                                         bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   vmm_ral_reg rg;

   set_by_name = 0;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return 0;

   rg.set(value);
   set_by_name = 1;
endfunction: set_by_name
	

function bit vmm_ral_access::get_by_name(input string                         name,
                                         output bit [`VMM_RAL_DATA_WIDTH-1:0] value);
   vmm_ral_reg rg;

   get_by_name = 0;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return 0;

   value = rg.get();
   get_by_name = 1;
endfunction: get_by_name
	

task vmm_ral_access::write_by_name(output vmm_rw::status_e              status,
                                   input  string                        name,
                                   input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                   input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                   input  string                        domain = "",
                                   input  int                           data_id = -1,
                                   input  int                           scenario_id = -1,
                                   input  int                           stream_id = -1,
                                   input  string                        fname = "",
                                   input  int                           lineno = 0
                    );
   vmm_ral_reg rg;
   this.fname = fname;
   this.lineno = lineno;

   status = vmm_rw::ERROR;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return;

   rg.write(status, data, path, domain, data_id, scenario_id, stream_id);
endtask: write_by_name


task vmm_ral_access::read_by_name(output vmm_rw::status_e              status,
                                  input  string                        name,
                                  output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                  input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                  input  string                        domain = "",
                                  input  int                           data_id = -1,
                                  input  int                           scenario_id = -1,
                                  input  int                           stream_id = -1,
                                  input  string                        fname = "",
                                  input  int                           lineno = 0
                    );
   vmm_ral_reg rg;
   this.fname = fname;
   this.lineno = lineno;

   status = vmm_rw::ERROR;
   rg = this.model.get_reg_by_name(name);
   if (rg == null) return;

   rg.read(status, data, path, domain, data_id, scenario_id, stream_id);
endtask: read_by_name


task vmm_ral_access::write_mem_by_name(output vmm_rw::status_e              status,
                                       input  string                        name,
                                       input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                       input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                       input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                       input  string                        domain = "",
                                       input  int                           data_id = -1,
                                       input  int                           scenario_id = -1,
                                       input  int                           stream_id =-1,
                                       input  string                        fname = "",
                                       input  int                           lineno = 0
                    );
   vmm_ral_mem mem;
   this.fname = fname;
   this.lineno = lineno;

   status = vmm_rw::ERROR;
   mem = this.model.get_mem_by_name(name);
   if (mem == null) return;

   mem.write(status, offset, data, path, domain, data_id, scenario_id, stream_id);
endtask: write_mem_by_name


task vmm_ral_access::read_mem_by_name(output vmm_rw::status_e              status,
                                      input  string                        name,
                                      input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                      output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                      input  vmm_ral::path_e               path = vmm_ral::DEFAULT,
                                      input  string                        domain = "",
                                      input  int                           data_id = -1,
                                      input  int                           scenario_id = -1,
                                      input  int                           stream_id = -1,
                                      input  string                        fname = "",
                                      input  int                           lineno = 0
                    );
   vmm_ral_mem mem;
   this.fname = fname;
   this.lineno = lineno;

   status = vmm_rw::ERROR;
   mem = this.model.get_mem_by_name(name);
   if (mem == null) return;

   mem.read(status, offset, data, path, domain, data_id, scenario_id, stream_id);
endtask: read_mem_by_name


//
// Identify the sequence of addresses that must be accessed physically
// to access the specified number of bytes at the specified address
// within the specified block or system. Returns the number of bytes
// of valid data in each access.
//
// Returns a list of address in little endian order, with the granularity
// of the top-level system
//
// A register is specified as a base address with mem_indx == 0.
// A location within a memory is specified as an index from a base address.
//
function int vmm_ral_access::Xget_physical_addressesX(bit [`VMM_RAL_ADDR_WIDTH-1:0]     base_addr,
                                                      bit [`VMM_RAL_ADDR_WIDTH-1:0]     mem_offset,
                                                      int unsigned                      n_bytes,
                                                      vmm_ral_block_or_sys              in_block,
                                                      string                            domain,
                                                      int                               n_used_bytes, 
                                                      ref bit [`VMM_RAL_ADDR_WIDTH-1:0] addr[]);
   int bus_width = in_block.get_n_bytes(domain);
   bit [`VMM_RAL_ADDR_WIDTH-1:0] local_addr[];
   vmm_ral_block_or_sys          parent = in_block.get_parent();
   bit byte_level_addr_granularity = in_block.is_byte_level_addr_granularity();

   addr = new [0];

   if (n_bytes <= 0) begin
      `vmm_fatal(this.log, $psprintf("Cannot access %0d bytes. Must be greater than 0",
                                     n_bytes));
      return 0;
   end

   // First, identify the addresses within the block/system
   if (n_bytes <= bus_width) begin
      local_addr = new [1];
      local_addr[0] = base_addr + mem_offset;

   end else begin
      int n;

      n = ((n_bytes-1) / bus_width) + 1;

      local_addr = new [n];
      
      base_addr = base_addr + mem_offset * n;

      case (in_block.get_endian(domain))
         vmm_ral::LITTLE_ENDIAN: begin
            foreach (local_addr[i]) begin
               if (byte_level_addr_granularity)
                  local_addr[i] = base_addr + i * bus_width;
               else
                  local_addr[i] = base_addr + i;
            end
         end
         vmm_ral::BIG_ENDIAN: begin
            foreach (local_addr[i]) begin
               n--;
               if (byte_level_addr_granularity)
                  local_addr[i] = base_addr + n * bus_width;
               else
                  local_addr[i] = base_addr + n;
            end
         end
         vmm_ral::LITTLE_FIFO: begin
            foreach (local_addr[i]) begin
               local_addr[i] = base_addr;
            end
         end
         vmm_ral::BIG_FIFO: begin
            foreach (local_addr[i]) begin
               local_addr[i] = base_addr;
            end
         end
         default: begin
            `vmm_error(this.log, $psprintf("Block has no specified endianness. Cannot access %0d bytes register via its %0d byte \"%s\" interface",
                                           n_bytes, in_block.get_n_bytes(domain), domain));
         end
      endcase
   end

   // Get rid of addr, that do not contribute to the data
   if (byte_level_addr_granularity && n_used_bytes > 0) begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] tmp_local_addr[];
      int tmp_n = ((n_used_bytes-1) / bus_width) + 1;

      tmp_local_addr = new [tmp_n];
      foreach (local_addr[i]) begin
         if (i < tmp_n) tmp_local_addr[i] = local_addr[i];
      end
      local_addr = new [tmp_n] (tmp_local_addr);
   end

   // Then translate these addresses in the parent's space
   if (parent == null) begin
      // This is the top-most system/block!
      addr = new [local_addr.size()] (local_addr);
      foreach(addr[i])
        addr[i] = addr[i]+in_block.get_base_addr(domain);
   end else begin
      bit [`VMM_RAL_ADDR_WIDTH-1:0] sys_addr[];
      bit [`VMM_RAL_ADDR_WIDTH-1:0] base_addr;
      string                        up_domain;
      int w, k;
      int parent_n_bytes;

      up_domain = in_block.get_parent_domain(domain);
      parent_n_bytes = parent.get_n_bytes(up_domain);

      // Scale the consecutive local address in the system's granularity
      if (bus_width < parent_n_bytes) k = 1;
      else k = ((bus_width-1) / parent_n_bytes) + 1;

      base_addr = in_block.get_base_addr(domain);
      foreach (local_addr[i]) begin
         int n = addr.size();
         bit [`VMM_RAL_ADDR_WIDTH-1:0] new_sys_addr;

         if (byte_level_addr_granularity) begin
            new_sys_addr = base_addr + ((local_addr[i] / bus_width) 
                                        * parent_n_bytes) 
                                     * k + local_addr[i] % bus_width;

            if (n_used_bytes > 0) 
               n_used_bytes = (n_used_bytes > bus_width) ? bus_width : n_used_bytes; 
            else n_used_bytes = (n_bytes > bus_width) ? bus_width : n_bytes; 
         end
         else new_sys_addr = base_addr + local_addr[i] * k;

         w = this.Xget_physical_addressesX(new_sys_addr, 0,
                                           bus_width, parent, up_domain,
                                           n_used_bytes, sys_addr);

         addr = new [n + sys_addr.size()] (addr);
         foreach (sys_addr[j]) begin
            addr[n+j] = sys_addr[j];
         end
      end
      // The width of each access is the minimum of this block or the system's width
      if (w < bus_width) bus_width = w;
   end

`ifdef TESTING_Xget_physical_addressesX
   begin
      vmm_ral_block bbb;

      if ($cast(bbb, in_block)) begin
         foreach (addr[i]) begin
            $display("DEBUG Message: Top level addr[%0d] of reg/mem in block %s = %h\n", 
                     i, in_block.get_fullname(), addr[i]);
         end
         $display("bus_width = %d\n", bus_width);
      end
   end
`endif

   Xget_physical_addressesX = bus_width;
endfunction: Xget_physical_addressesX

function bit vmm_ral_access::Xsupports_byte_enableX(string   domain = "");
   if(this.rw_exec[domain]!=null) 
   Xsupports_byte_enableX = this.rw_exec[domain].supports_byte_enable();
   return Xsupports_byte_enableX;

endfunction: Xsupports_byte_enableX 

