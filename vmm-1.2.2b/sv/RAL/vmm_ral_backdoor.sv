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
// CLASS: vmm_ral_reg_backdoor_callbacks
// Façade class for register backdoor access callback methods. 
//------------------------------------------------------------------------------
virtual class vmm_ral_reg_backdoor_callbacks; 

    string fname = "";
    int lineno = 0;


   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This callback method is invoked before a value is read from a register through backdoor.
   //
   // This callback method is invoked when the <vmm_ral_reg_backdoor::pre_read()> method
   // is invoked. 
   //------------------------------------------------------------------------------
	extern virtual task pre_read(input vmm_ral_reg rg, 
                                     input int data_id = -1, 
                                     input int scenario_id = -1, 
                                     input int stream_id = -1); 


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This callback method is invoked after a value is read from a register through backdoor.
   //
   // This callback method is invoked when the <vmm_ral_reg_backdoor::post_read()> method
   // is invoked. 
   //------------------------------------------------------------------------------
	extern virtual task post_read(input vmm_ral_reg rg, 
                                      inout vmm_rw::status_e status, 
                                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                      input int data_id = -1, 
                                      input int scenario_id = -1, 
                                      input int stream_id = -1); 


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This callback method is invoked before a value is written to a register through backdoor.
   //
   // The written value, if modified, modifies the actual value that will be written.
   //
   // This callback method is invoked when the <vmm_ral_reg_backdoor::pre_write()> is invoked.
   // 
   //------------------------------------------------------------------------------
	extern virtual task pre_write(input vmm_ral_reg rg, 
                                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                      input int data_id = -1, 
                                      input int scenario_id = -1, 
                                      input int stream_id = -1); 


   //------------------------------------------------------------------------------
   // TASK: post_write
   // This callback method is invoked after a value is written to a register through backdoor.
   //
   // This callback method is invoked when the <vmm_ral_reg_backdoor::post_write()> method
   // is invoked. 
   //------------------------------------------------------------------------------
	extern virtual task post_write(input vmm_ral_reg rg, 
                                       inout vmm_rw::status_e status, 
                                       input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                       input int data_id = -1, 
                                       input int scenario_id = -1, 
                                       input int stream_id = -1); 

	extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] encode(bit [`VMM_RAL_DATA_WIDTH-1:0] data); 

	extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] decode(bit [`VMM_RAL_DATA_WIDTH-1:0] data); 


endclass: vmm_ral_reg_backdoor_callbacks


task vmm_ral_reg_backdoor_callbacks::pre_read(input vmm_ral_reg rg, 
		                              input int data_id = -1, 
		                              input int scenario_id = -1, 
		                              input int stream_id = -1);

endtask: pre_read


task vmm_ral_reg_backdoor_callbacks::post_read(input vmm_ral_reg rg, 
					       inout vmm_rw::status_e status, 
					       inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					       input int data_id = -1, 
					       input int scenario_id = -1, 
					       input int stream_id = -1);

endtask: post_read


task vmm_ral_reg_backdoor_callbacks::pre_write(input vmm_ral_reg rg, 
					       inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					       input int data_id = -1, 
					       input int scenario_id = -1, 
					       input int stream_id = -1);

endtask: pre_write


task vmm_ral_reg_backdoor_callbacks::post_write(input vmm_ral_reg rg, 
				                inout vmm_rw::status_e status, 
				                input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				                input int data_id = -1, 
				                input int scenario_id = -1, 
				                input int stream_id = -1); 

endtask: post_write


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_reg_backdoor_callbacks::encode(bit [`VMM_RAL_DATA_WIDTH-1:0] data);

endfunction: encode


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_reg_backdoor_callbacks::decode(bit [`VMM_RAL_DATA_WIDTH-1:0] data);

endfunction: decode





//------------------------------------------------------------------------------
// CLASS: vmm_ral_mem_backdoor_callbacks
// Façade class for memory backdoor access callback methods. 
//------------------------------------------------------------------------------
virtual class vmm_ral_mem_backdoor_callbacks; 
    
	string fname = "";
        int lineno = 0;
	

   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This callback method is invoked before a value is read from a memory through backdoor.
   //
   // This callback method is invoked when the <vmm_ral_mem_backdoor::pre_read()> method
   // is invoked. 
   //------------------------------------------------------------------------------
	extern virtual task pre_read(input vmm_ral_mem mem,
                                     inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                     input int data_id = -1, 
                                     input int scenario_id = -1, 
                                     input int stream_id = -1); 


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This callback method is invoked after a value is read from a memory through backdoor.
   //
   // This callback method is invoked when the <vmm_ral_mem_backdoor::post_read()> method
   // is invoked. 
   //------------------------------------------------------------------------------
	extern virtual task post_read(input vmm_ral_mem mem, 
		                      inout vmm_rw::status_e status, 
		                      inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
		                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
		                      input int data_id = -1, 
		                      input int scenario_id = -1, 
		                      input int stream_id = -1); 


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This callback method is invoked before a value is written to a memory through backdoor.
   //
   // The written value, if modified, modifies the actual value that will be written. This
   // callback method is invoked when the <vmm_ral_mem_backdoor::pre_write()> is invoked.
   // 
   //------------------------------------------------------------------------------
	extern virtual task pre_write(input vmm_ral_mem mem, 
			              inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
			              inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
			              input int data_id = -1, 
			              input int scenario_id = -1, 
			              input int stream_id= -1); 


   //------------------------------------------------------------------------------
   // TASK: post_write
   // 
   //------------------------------------------------------------------------------
	extern virtual task post_write(input vmm_ral_mem mem, 
				       inout vmm_rw::status_e status, 
				       inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
				       input bit [`VMM_RAL_DATA_WIDTH-1:0] data,   
				       input int data_id = -1, 
				       input int scenario_id = -1, 
				       input int stream_id = -1); 

	extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] encode(bit [`VMM_RAL_DATA_WIDTH-1:0] data); 

	extern virtual function bit [`VMM_RAL_DATA_WIDTH-1:0] decode(bit [`VMM_RAL_DATA_WIDTH-1:0] data); 

endclass: vmm_ral_mem_backdoor_callbacks


task vmm_ral_mem_backdoor_callbacks::pre_read(input vmm_ral_mem mem, 
					      inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
					      input int data_id = -1, 
					      input int scenario_id = -1, 
					      input int stream_id = -1);

endtask: pre_read


task vmm_ral_mem_backdoor_callbacks::post_read(input vmm_ral_mem mem, 
					       inout vmm_rw::status_e status, 
					       inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
					       inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					       input int data_id = -1, 
					       input int scenario_id = -1, 
					       input int stream_id = -1);

endtask: post_read


task vmm_ral_mem_backdoor_callbacks::pre_write(input vmm_ral_mem mem, 
					       inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
					       inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					       input int data_id = -1, 
					       input int scenario_id = -1, 
					       input int stream_id = -1);

endtask: pre_write


task vmm_ral_mem_backdoor_callbacks::post_write(input vmm_ral_mem mem, 
					        inout vmm_rw::status_e status, 
					        inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
					        input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					        input int data_id = -1, 
					        input int scenario_id = -1, 
					        input int stream_id = -1); 

endtask: post_write


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_mem_backdoor_callbacks::encode(bit [`VMM_RAL_DATA_WIDTH-1:0] data);

endfunction: encode


function bit [`VMM_RAL_DATA_WIDTH-1:0] vmm_ral_mem_backdoor_callbacks::decode(bit [`VMM_RAL_DATA_WIDTH-1:0] data);

endfunction: decode




//------------------------------------------------------------------------------
// CLASS: vmm_ral_reg_backdoor
// Virtual base class for back-door access to registers. Extensions of this class are
// automatically generated by RAL if full hierarchical paths to registers are specified
// through the hdl_path properties in RALF descriptions. Can be extended by users to provide
// user-specific back-door access to registers that are not implemented in pure SystemVerilog.
// 
//------------------------------------------------------------------------------
virtual class vmm_ral_reg_backdoor;
   string fname = "";
   int lineno = 0;
   vmm_ral_reg rg;
   local vmm_ral_reg_backdoor_callbacks backdoor_callbacks[$];

   static vmm_log log = new("vmm_ral_reg_backdoor", "class");
   
   local process update_thread;
   
   extern function new(input vmm_ral_reg rg=null);
    

   //------------------------------------------------------------------------------
   // TASK: write
   // Deposit the specified value in the register corresponding to the instance of this class.
   //
   // Returns an indication of the success of the operation. The values of the arguments:
   // data_id scenario_id stream_id 
   //------------------------------------------------------------------------------
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);


   //------------------------------------------------------------------------------
   // TASK: read
   // Peek the current value of the register corresponding to the instance of this class.
   //
   // Returns the content of the register and an indication of the success of the operation.
   // The value of the arguments: data_id scenario_id stream_id 
   //------------------------------------------------------------------------------
   extern virtual task read(output vmm_rw::status_e              status,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern virtual function bit is_auto_updated(string fieldname);

   extern virtual task wait_for_change();

   extern function void start_update_thread(vmm_ral_reg rg);

   extern function void kill_update_thread();


   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This method invokes all the registered vmm_ral_reg_backdoor_callbacks::pre_read()
   // methods in the order of their registration.
   //
   // This method should be invoked just before
   // executing any backdoor read operation. ralgen generated auto backdoor read/write
   // code takes care of this, by invoking this method just before reading any data through
   // backdoor.
   //
   // User defined backdoors will need to take care of this. 
   //------------------------------------------------------------------------------
   extern virtual task pre_read(input int data_id = -1, 
				         		input int scenario_id = -1, 
	  			                input int stream_id = -1);


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This method invokes all registered <vmm_ral_reg_backdoor_callbacks::decode()>
   // methods in the reverse order of their registration.
   //
   // And after that, it invokes all the
   // registered <vmm_ral_reg_backdoor_callbacks::post_read()> methods in the order
   // of their registration. 
   //------------------------------------------------------------------------------
   extern virtual task post_read(inout vmm_rw::status_e status, 
                                 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				          		 input int data_id = -1, 
				          		 input int scenario_id = -1, 
				          		 input int stream_id = -1);
   

   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This method invokes all the registered <vmm_ral_reg_backdoor_callbacks::pre_write()>
   // methods in the order of their registration. And then, it invokes all the registered
   // vmm_ral_reg_backdoor_callbacks::encode() methods in the order of their registration.
   //
   // Ideally, you should invoke this method before executing any backdoor write operation.
   // ralgen generated auto backdoor read/ write code takes care of this by invoking this
   // method just before 
   //------------------------------------------------------------------------------
   extern virtual task pre_write(inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);
   

   //------------------------------------------------------------------------------
   // TASK: post_write
   // This method invokes all the registered <vmm_ral_reg_backdoor_callbacks::post_write()>
   // methods in the order of their registration. This method should be invoked just after
   // executing any backdoor write operation. ralgen generated auto backdoor read/write
   // code takes care of this, by invoking this method just after writing any data through
   // backdoor.
   //
   // User defined backdoors will need to take care of this. 
   //------------------------------------------------------------------------------
   extern virtual task post_write(inout vmm_rw::status_e status, 
				           		  input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				           		  input int data_id = -1, 
				           		  input int scenario_id = -1, 
				           		  input int stream_id = -1); 
   

   //------------------------------------------------------------------------------
   // FUNCTION: append_callback
   // Appends the specified callback extension instance to the list of registered callbacks
   // of this register backdoor access class. Unless you specify explicitly, all the callback
   // methods are invoked in the order of the registration of their corresponding callback
   // class extension instance. 
   //------------------------------------------------------------------------------
   extern virtual function void append_callback(vmm_ral_reg_backdoor_callbacks cb, 
					        string fname = "",
					        int lineno = 0); 
   

   //------------------------------------------------------------------------------
   // FUNCTION: prepend_callback
   // Prepends the specified callback extension instance to the list of registered callbacks
   // of this register backdoor access class. Callbacks are invoked in the reverse order
   // of registration. 
   //------------------------------------------------------------------------------
   extern virtual function void prepend_callback(vmm_ral_reg_backdoor_callbacks cb, 
					         string fname = "",
					         int lineno = 0); 
   

   //------------------------------------------------------------------------------
   // FUNCTION: unregister_callback
   // Removes the specified callback extension instance from the registered callbacks
   // for this register backdoor access class. A warning message is issued if the callback
   // instance has not been previously registered. 
   //------------------------------------------------------------------------------
   extern virtual function void unregister_callback(vmm_ral_reg_backdoor_callbacks cb, 
					            string fname = "",
					            int lineno = 0);

endclass: vmm_ral_reg_backdoor

function bit vmm_ral_reg_backdoor::is_auto_updated(string fieldname);
   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::is_auto_updated() method has not been overloaded");
endfunction

task vmm_ral_reg_backdoor::wait_for_change();
   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::wait_for_change() method has not been overloaded");
endtask

function void vmm_ral_reg_backdoor::start_update_thread(vmm_ral_reg rg);
   if (this.update_thread != null) begin
      this.kill_update_thread();
   end

   fork
      begin
         vmm_ral_field fields[];

         this.update_thread = process::self();
         rg.get_fields(fields);
         forever begin
            vmm_rw::status_e status;
            bit [`VMM_RAL_DATA_WIDTH-1:0] val;
            this.read(status, val, -1, -1, -1);
            if (status != vmm_rw::IS_OK && status != vmm_rw::HAS_X) begin
               `vmm_error(this.log, $psprintf("Backdoor read of register '%s' failed.",
                          rg.get_name()));
            end
            foreach (fields[i]) begin
               if (this.is_auto_updated(fields[i].get_name())) begin
                  bit [`VMM_RAL_DATA_WIDTH-1:0] fld_val 
                     = val >> fields[i].get_lsb_pos_in_register();
                  fld_val = fld_val & ((1 << fields[i].get_n_bits())-1);
                  void'(fields[i].predict(fld_val));
               end 
            end
            this.wait_for_change();
         end
      end
   join_none
endfunction

function void vmm_ral_reg_backdoor::kill_update_thread();
   if (this.update_thread != null) begin
      this.update_thread.kill();
      this.update_thread = null;
   end
endfunction


//------------------------------------------------------------------------------
// CLASS: vmm_ral_mem_backdoor
// Virtual base class for back-door access to memories. Extensions of this class are automatically
// generated by RAL if full hierarchical paths to memories are specified through the hdl_path
// properties in RALF descriptions. Can be extended by users to provide user-specific
// back-door access to memories that are not implemented in pure SystemVerilog. 
//------------------------------------------------------------------------------
virtual class vmm_ral_mem_backdoor;
   string fname = "";
   int lineno = 0;
   vmm_ral_mem mem;
   local vmm_ral_mem_backdoor_callbacks backdoor_callbacks[$];
   static vmm_log log = new("vmm_ral_mem_backdoor", "class");
   
   extern function new(input vmm_ral_mem mem=null);


   //------------------------------------------------------------------------------
   // TASK: write
   // Deposit the specified value at the specified offset of the memory corresponding to
   // the instance of this class. Returns an indication of the success of the operation. The
   // values of the arguments: data_id scenario_id stream_id 
   //------------------------------------------------------------------------------
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);
   

   //------------------------------------------------------------------------------
   // TASK: read
   // Peek the current value at the specified offset in the memory corresponding to the instance
   // of this class. Returns the content of the memory location and an indication of the success
   // of the operation. The values of the arguments: data_id scenario_id stream_id 
   //------------------------------------------------------------------------------
   extern virtual task read(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);
   

   //------------------------------------------------------------------------------
   // TASK: pre_read
   // This method invokes all the registered <vmm_ral_mem_backdoor_callbacks::pre_read()>
   // methods in the order of their registration. This method should be invoked just before
   // executing any backdoor read operation. ralgen generated auto backdoor read/write
   // code takes care of this by invoking this method just before reading any data through
   // backdoor. 
   //
   // User defined backdoors should take care of this. The offset, if modified
   // by this method modifies the actual memory location i.e. the offset that is read. 
   //------------------------------------------------------------------------------
   extern virtual task pre_read(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                input int data_id = -1, 
                                input int scenario_id = -1, 
                                input int stream_id = -1);


   //------------------------------------------------------------------------------
   // TASK: post_read
   // This method invokes all the registered <vmm_ral_mem_backdoor_callbacks::decode()>
   // methods in the reverse order of their registration. And then, it invokes all the registered
   // vmm_ral_mem_backdoor_callbacks::post_read() methods in the order of their registration.
   // 
   //------------------------------------------------------------------------------
   extern virtual task post_read(inout vmm_rw::status_e status, 
					  			 inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
					  			 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);


   //------------------------------------------------------------------------------
   // TASK: pre_write
   // This method invokes all the registered <vmm_ral_mem_backdoor_callbacks::pre_write()>
   // methods in the order of their registration. And then, it invokes all the registered
   // <vmm_ral_mem_backdoor_callbacks::encode()> methods in the order of their registration.
   // This method should be invoked just before executing any backdoor write operation.
   // ralgen generated auto backdoor read/write code takes care of this by invoking this
   // method just before writing any data 
   //------------------------------------------------------------------------------
   extern virtual task pre_write(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
					  			 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);
	

   //------------------------------------------------------------------------------
   // TASK: post_write
   // This method invokes all the registered <vmm_ral_mem_backdoor_callbacks::post_write()>
   // methods in the order of their registration. This method should be invoked just after
   // executing any backdoor write operation. ralgen generated auto backdoor read/write
   // code takes care of this by invoking this method just after writing any data through backdoor.
   // User defined backdoors should take care of this. 
   //------------------------------------------------------------------------------
   extern virtual task post_write(inout vmm_rw::status_e status, 
				           		  inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
				           		  input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				           		  input int data_id = -1, 
				           		  input int scenario_id = -1, 
				           		  input int stream_id = -1); 

   extern virtual function void append_callback(vmm_ral_mem_backdoor_callbacks cb, 
					        string fname = "",
					        int lineno = 0);
   

   //------------------------------------------------------------------------------
   // FUNCTION: prepend_callback
   // Prepends the specified callback extension instance to the registered callbacks for
   // this memory backdoor access class. Callbacks are invoked in the reverse order of registration.
   // 
   //------------------------------------------------------------------------------
   extern virtual function void prepend_callback(vmm_ral_mem_backdoor_callbacks cb, 
						 string fname = "",
						 int lineno = 0); 


   //------------------------------------------------------------------------------
   // FUNCTION: unregister_callback
   // Removes the specified callback extension instance from the registered callbacks
   // for this memory backdoor access class. A warning message is issued if the callback instance
   // has not been previously stored. 
   //------------------------------------------------------------------------------
   extern virtual function void unregister_callback(vmm_ral_mem_backdoor_callbacks cb, 
						    string fname = "",
						    int lineno = 0);

endclass: vmm_ral_mem_backdoor


function vmm_ral_reg_backdoor::new(input vmm_ral_reg rg=null);

	this.rg = rg;

endfunction: new


task vmm_ral_reg_backdoor::write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);

   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::write() method has not been overloaded");
   
endtask: write


task vmm_ral_reg_backdoor::read(output vmm_rw::status_e              status,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1);

   `vmm_fatal(this.log, "vmm_ral_reg_backdoor::read() method has not been overloaded");
   
endtask: read


task vmm_ral_reg_backdoor::pre_read(input int data_id = -1, 
					     input int scenario_id = -1, 
					     input int stream_id = -1);

    foreach (this.backdoor_callbacks[i]) 
     begin
       this.backdoor_callbacks[i].pre_read(this.rg, data_id, scenario_id, stream_id);
     end

endtask: pre_read


task vmm_ral_reg_backdoor::post_read(inout vmm_rw::status_e status, 
			                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
			                      input int data_id = -1, 
			                      input int scenario_id = -1, 
			                      input int stream_id = -1);

    vmm_ral_reg_backdoor_callbacks tmp_backdoor_callbacks[$];
	vmm_ral_reg_backdoor_callbacks temp[$]; 
	int tmp_size;
	
    tmp_backdoor_callbacks = this.backdoor_callbacks;
`ifdef VCS
      if (tmp_backdoor_callbacks.size() > 1) tmp_backdoor_callbacks.reverse();
	`else //Simplifying the code to ensure non-VCS simulators can compile it
	  if (tmp_backdoor_callbacks.size() > 1) begin
	   tmp_size = tmp_backdoor_callbacks.size();
       for(int tmp_idx = tmp_size - 1, int indx = 0 ; tmp_idx >=0 ; tmp_idx -- ,indx++) 
		 begin
		      temp[indx] = tmp_backdoor_callbacks[tmp_idx];
		 end
	  end
	tmp_backdoor_callbacks = temp;

	`endif
    foreach (tmp_backdoor_callbacks[i]) 
     begin
       data = tmp_backdoor_callbacks[i].decode(data);
     end
    foreach (this.backdoor_callbacks[i]) 
     begin
       this.backdoor_callbacks[i].post_read(this.rg, status, data, data_id, scenario_id, stream_id);
     end

endtask: post_read


task vmm_ral_reg_backdoor::pre_write(inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                              input int data_id = -1, 
                                              input int scenario_id = -1, 
                                              input int stream_id = -1);

    foreach (this.backdoor_callbacks[i]) 
     begin
       this.backdoor_callbacks[i].pre_write(this.rg, data, data_id, scenario_id, stream_id);
     end
    foreach (this.backdoor_callbacks[i]) 
     begin
       data = this.backdoor_callbacks[i].encode(data);
     end
		
endtask: pre_write


task vmm_ral_reg_backdoor::post_write(inout vmm_rw::status_e status, 
                                               input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                               input int data_id = -1, 
                                               input int scenario_id = -1, 
                                               input int stream_id = -1); 

     foreach (this.backdoor_callbacks[i]) 
      begin
        this.backdoor_callbacks[i].post_write(this.rg, status, data, data_id, scenario_id, stream_id);
      end	

endtask: post_write


function void vmm_ral_reg_backdoor::append_callback(vmm_ral_reg_backdoor_callbacks cb, 
                                                    string fname = "",
                                                    int lineno = 0); 

     foreach (this.backdoor_callbacks[i]) 
      begin
     	if (this.backdoor_callbacks[i] == cb) 
     	begin
          `vmm_warning(this.log, $psprintf("Callback has already been registered with register"));
      	  return;
     	end
      end
     
     /// Prepend new callback
      cb.fname = fname;
      cb.lineno = lineno;
      this.backdoor_callbacks.push_back(cb);	
		
endfunction: append_callback


function void vmm_ral_reg_backdoor::prepend_callback(vmm_ral_reg_backdoor_callbacks cb, 
		                                     string fname = "", 
		                                     int lineno = 0); 

     foreach (this.backdoor_callbacks[i]) 
      begin
        if (this.backdoor_callbacks[i] == cb) 
	 begin
	   `vmm_warning(this.log, $psprintf("Callback has already been registered with register"));
           return;
	 end
      end
			
      // Prepend new callback
      cb.fname = fname;
      cb.lineno = lineno;
      this.backdoor_callbacks.push_front(cb);	
		
endfunction: prepend_callback



function void vmm_ral_reg_backdoor::unregister_callback(vmm_ral_reg_backdoor_callbacks cb,
				                        string fname = "",
				                        int lineno = 0);

     foreach (this.backdoor_callbacks[i]) 
      begin
        if (this.backdoor_callbacks[i] == cb) 
	 begin
	   int j = i;
           // Unregister it
    	   this.backdoor_callbacks.delete(j);
	   return;
    	 end
      end

   `vmm_warning(this.log, $psprintf("Callback was not registered with register "));

endfunction: unregister_callback


function vmm_ral_mem_backdoor::new(input vmm_ral_mem mem=null);
    this.mem = mem;
endfunction: new

task vmm_ral_mem_backdoor::write(output vmm_rw::status_e              status,
                                 input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                 input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                 input  int                           data_id = -1,
                                 input  int                           scenario_id = -1,
                                 input  int                           stream_id = -1);

   `vmm_fatal(this.log, "vmm_ral_mem_backdoor::write() method has not been overloaded");
   
endtask: write


task vmm_ral_mem_backdoor::read(output vmm_rw::status_e              status,
                                input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                                input  int                           data_id = -1,
                                input  int                           scenario_id = -1,
                                input  int                           stream_id = -1);

   `vmm_fatal(this.log, "vmm_ral_mem_backdoor::read() method has not been overloaded");
   
endtask: read


task vmm_ral_mem_backdoor::pre_read(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                             input int data_id = -1, 
                                             input int scenario_id = -1, 
                                             input int stream_id = -1);

     foreach (this.backdoor_callbacks[i]) 
      begin
        this.backdoor_callbacks[i].pre_read(this.mem, offset, data_id, scenario_id, stream_id);
      end

endtask: pre_read


task vmm_ral_mem_backdoor::post_read(inout vmm_rw::status_e status, 
                                              inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                              inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                              input int data_id = -1, 
                                              input int scenario_id = -1, 
                                              input int stream_id = -1);

    vmm_ral_mem_backdoor_callbacks tmp_backdoor_callbacks[$];
	vmm_ral_mem_backdoor_callbacks temp[$]; 
	int tmp_size;
    tmp_backdoor_callbacks = this.backdoor_callbacks;

`ifdef VCS
      if (tmp_backdoor_callbacks.size() > 1) tmp_backdoor_callbacks.reverse();
     `else //Simplifying the code to ensure non-VCS simulators can compile it
      if (tmp_backdoor_callbacks.size() > 1) begin
       tmp_size = tmp_backdoor_callbacks.size();
          for(int tmp_idx = tmp_size - 1, int indx = 0 ; tmp_idx >=0 ; tmp_idx -- ,indx++) 
          begin
             temp[indx] = tmp_backdoor_callbacks[tmp_idx];
          end 
       end
      tmp_backdoor_callbacks = temp;
	 `endif

    foreach (tmp_backdoor_callbacks[i]) 
     begin
        data = tmp_backdoor_callbacks[i].decode(data);
     end
    foreach (this.backdoor_callbacks[i]) 
     begin
        this.backdoor_callbacks[i].post_read(this.mem, status, offset, data, data_id, scenario_id, stream_id);
      end

endtask: post_read


task vmm_ral_mem_backdoor::pre_write(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                              inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                              input int data_id = -1, 
                                              input int scenario_id = -1, 
                                              input int stream_id = -1);

     foreach (this.backdoor_callbacks[i]) 
      begin
        this.backdoor_callbacks[i].pre_write(this.mem, offset, data, data_id, scenario_id, stream_id);
      end
     foreach (this.backdoor_callbacks[i]) 
      begin
        data = this.backdoor_callbacks[i].encode(data);
      end
		
endtask: pre_write


task vmm_ral_mem_backdoor::post_write(inout vmm_rw::status_e status, 
                                               inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                                               input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                               input int data_id = -1, 
                                               input int scenario_id = -1, 
                                               input int stream_id = -1); 

     foreach (this.backdoor_callbacks[i]) 
      begin
        this.backdoor_callbacks[i].post_write(this.mem, status, offset, data, data_id, scenario_id, stream_id);
      end	

endtask: post_write


function void vmm_ral_mem_backdoor::append_callback(vmm_ral_mem_backdoor_callbacks cb, 
                                                    string fname = "", 
                                                    int lineno = 0); 

     foreach (this.backdoor_callbacks[i]) 
      begin
        if (this.backdoor_callbacks[i] == cb) 
         begin
           `vmm_warning(this.log, $psprintf("Callback has already been registered with register"));
           return;
         end
      end
     
     // Prepend new callback
     cb.fname = fname;
     cb.lineno = lineno;
     this.backdoor_callbacks.push_back(cb);	
		
endfunction: append_callback


function void vmm_ral_mem_backdoor::prepend_callback(vmm_ral_mem_backdoor_callbacks cb, 
                                                     string fname = "", 
                                                     int lineno = 0); 

     foreach (this.backdoor_callbacks[i]) 
      begin
        if (this.backdoor_callbacks[i] == cb) 
         begin
           `vmm_warning(this.log, $psprintf("Callback has already been registered with register"));
           return;
         end
      end
             		
     // Prepend new callback
     cb.fname = fname;
     cb.lineno = lineno;
     this.backdoor_callbacks.push_front(cb);	
		
endfunction: prepend_callback



function void vmm_ral_mem_backdoor::unregister_callback(vmm_ral_mem_backdoor_callbacks cb,
                                                        string fname = "", 
                                                        int lineno = 0);

     foreach (this.backdoor_callbacks[i]) 
      begin
        if (this.backdoor_callbacks[i] == cb) 
         begin
           int j = i;
           // Unregister it
           this.backdoor_callbacks.delete(j);
           return;
         end
      end

     `vmm_warning(this.log, $psprintf("Callback was not registered with register "));

endfunction: unregister_callback

