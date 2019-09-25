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

virtual class vmm_ral_reg_backdoor_callbacks; 

    string fname = "";
    int lineno = 0;

	extern virtual task pre_read(input vmm_ral_reg rg, 
                                     input int data_id = -1, 
                                     input int scenario_id = -1, 
                                     input int stream_id = -1); 

	extern virtual task post_read(input vmm_ral_reg rg, 
                                      inout vmm_rw::status_e status, 
                                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                      input int data_id = -1, 
                                      input int scenario_id = -1, 
                                      input int stream_id = -1); 

	extern virtual task pre_write(input vmm_ral_reg rg, 
                                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
                                      input int data_id = -1, 
                                      input int scenario_id = -1, 
                                      input int stream_id = -1); 

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




virtual class vmm_ral_mem_backdoor_callbacks; 
    
	string fname = "";
        int lineno = 0;
	
	extern virtual task pre_read(input vmm_ral_mem mem,
                                     inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                     input int data_id = -1, 
                                     input int scenario_id = -1, 
                                     input int stream_id = -1); 

	extern virtual task post_read(input vmm_ral_mem mem, 
		                      inout vmm_rw::status_e status, 
		                      inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
		                      inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
		                      input int data_id = -1, 
		                      input int scenario_id = -1, 
		                      input int stream_id = -1); 

	extern virtual task pre_write(input vmm_ral_mem mem, 
			              inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
			              inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
			              input int data_id = -1, 
			              input int scenario_id = -1, 
			              input int stream_id= -1); 

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



virtual class vmm_ral_reg_backdoor;
   string fname = "";
   int lineno = 0;
   vmm_ral_reg rg;
   local vmm_ral_reg_backdoor_callbacks backdoor_callbacks[$];

   static vmm_log log = new("vmm_ral_reg_backdoor", "class");
   
   local process update_thread;
   
   extern function new(input vmm_ral_reg rg=null);
    
   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);

   extern virtual task read(output vmm_rw::status_e              status,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);

   extern virtual function bit is_auto_updated(string fieldname);

   extern virtual task wait_for_change();

   extern function void start_update_thread(vmm_ral_reg rg);

   extern function void kill_update_thread();

   extern virtual task pre_read(input int data_id = -1, 
				         		input int scenario_id = -1, 
	  			                input int stream_id = -1);

   extern virtual task post_read(inout vmm_rw::status_e status, 
                                 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				          		 input int data_id = -1, 
				          		 input int scenario_id = -1, 
				          		 input int stream_id = -1);
   
   extern virtual task pre_write(inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);
   
   extern virtual task post_write(inout vmm_rw::status_e status, 
				           		  input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				           		  input int data_id = -1, 
				           		  input int scenario_id = -1, 
				           		  input int stream_id = -1); 
   
   extern virtual function void append_callback(vmm_ral_reg_backdoor_callbacks cb, 
					        string fname = "",
					        int lineno = 0); 
   
   extern virtual function void prepend_callback(vmm_ral_reg_backdoor_callbacks cb, 
					         string fname = "",
					         int lineno = 0); 
   
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
            if (status != vmm_rw::IS_OK) begin
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

virtual class vmm_ral_mem_backdoor;
   string fname = "";
   int lineno = 0;
   vmm_ral_mem mem;
   local vmm_ral_mem_backdoor_callbacks backdoor_callbacks[$];
   static vmm_log log = new("vmm_ral_mem_backdoor", "class");
   
   extern function new(input vmm_ral_mem mem=null);

   extern virtual task write(output vmm_rw::status_e              status,
                             input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                             input  bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                             input  int                           data_id = -1,
                             input  int                           scenario_id = -1,
                             input  int                           stream_id = -1);
   
   extern virtual task read(output vmm_rw::status_e              status,
                            input  bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
                            output bit [`VMM_RAL_DATA_WIDTH-1:0] data,
                            input  int                           data_id = -1,
                            input  int                           scenario_id = -1,
                            input  int                           stream_id = -1);
   
   extern virtual task pre_read(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset, 
                                input int data_id = -1, 
                                input int scenario_id = -1, 
                                input int stream_id = -1);

   extern virtual task post_read(inout vmm_rw::status_e status, 
					  			 inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
					  			 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);

   extern virtual task pre_write(inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
					  			 inout bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
					  			 input int data_id = -1, 
					  			 input int scenario_id = -1, 
					  			 input int stream_id = -1);
	
   extern virtual task post_write(inout vmm_rw::status_e status, 
				           		  inout bit [`VMM_RAL_ADDR_WIDTH-1:0] offset,
				           		  input bit [`VMM_RAL_DATA_WIDTH-1:0] data, 
				           		  input int data_id = -1, 
				           		  input int scenario_id = -1, 
				           		  input int stream_id = -1); 

   extern virtual function void append_callback(vmm_ral_mem_backdoor_callbacks cb, 
					        string fname = "",
					        int lineno = 0);
   
   extern virtual function void prepend_callback(vmm_ral_mem_backdoor_callbacks cb, 
						 string fname = "",
						 int lineno = 0); 

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

