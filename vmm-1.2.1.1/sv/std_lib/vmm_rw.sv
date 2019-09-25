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


function vmm_rw_burst::new(
   `ifdef VMM_12_UNDERPIN_VMM_DATA
      vmm_object parent = null, string name = ""
   `endif
   );
   `ifdef VMM_12_UNDERPIN_VMM_DATA
      super.new(parent, name);
   `endif
      this.linear.constraint_mode(0);
      this.fifo.constraint_mode(0);
      this.wrap.constraint_mode(0);
endfunction: new

function string vmm_rw_burst::psdisplay(string prefix = "");

   string fmt;
   string arg;
   if($value$plusargs("vmm_log_default=%s",arg)) begin
    if(arg=="VERBOSE") begin
      foreach(this.data[i]) begin
       fmt = {fmt,`vmm_sformatf("data[%0d] = %0h\n", i, data[i])};
      end
    end 
   end
   $sformat(psdisplay, {"%s%s @ 0x%h :: incr_addr = %0d, max_addr = %0d, n_beats = %0d \n", fmt }, prefix,
            kind.name(), addr, incr_addr, max_addr,this.n_beats);

endfunction: psdisplay

function vmm_rw_access::new(
   `ifdef VMM_12_UNDERPIN_VMM_DATA
      vmm_object parent = null, string name = ""
   `endif
   );
   `ifdef VMM_12_UNDERPIN_VMM_DATA
      super.new(this.log,parent, name);
   `else
      super.new(this.log);
   `endif
endfunction: new

function string vmm_rw_access::psdisplay(string prefix = "");
   string fmt;
   $sformat(fmt, "%0dh", this.n_bits);
   $sformat(psdisplay, {"%s%s @ 0x%h = %0d'h%", fmt, "\n"}, prefix,
            kind.name(), addr, n_bits, data);
endfunction: psdisplay


function vmm_rw_xactor::new(string                name,
                            string                inst,
                            int                   stream_id = -1,
                            vmm_rw_access_channel exec_chan = null);
   super.new(name, inst, stream_id);

   if (exec_chan == null) exec_chan = new({name, " Input Channel"}, inst);
   this.exec_chan = exec_chan;
			
   this.obsv_chan = new({name, " Output Channel"}, inst);
			
   this.log.is_above(this.exec_chan.log);
   this.log.is_above(this.obsv_chan.log);

   void'(this.notify.configure(BURST_DONE));
   void'(this.notify.configure(SINGLE_DONE));
endfunction: new


task vmm_rw_xactor::execute_single(vmm_rw_access tr);
   `vmm_fatal(this.log, "Undefined execute_single() method in vmm_rw_xactor extension");
endtask: execute_single

task vmm_rw_xactor::observe_single(output vmm_rw_access tr);
   // This methods doesnot return 
			wait(0);
endtask: observe_single

task vmm_rw_xactor::execute_burst(vmm_rw_burst tr);
   bit [`VMM_RW_ADDR_WIDTH-1:0] addr;
   int i;

   addr = tr.addr;
   i = 0;
   tr.status = vmm_rw::IS_OK;
   if (tr.kind == vmm_rw::READ) tr.data = new [tr.n_beats];
   repeat (tr.n_beats) begin
      vmm_rw_access s = new
      `ifdef VMM12_XACTOR_BASE
      `ifdef VMM_12_UNDERPIN_VMM_DATA
         (this, "ex_burst");
	  `else
	     ;
      `endif
	  `else
	     ;
      `endif

      s.kind = tr.kind;
      s.addr = addr;
      if (s.kind != vmm_rw::READ) s.data = tr.data[i++];
      this.execute_single(s);
      if (s.kind == vmm_rw::READ) tr.data[i++] = s.data;
      if (s.status != vmm_rw::IS_OK) begin
         tr.status = s.status;
         return;
      end

      addr += tr.incr_addr;
      if (addr > tr.max_addr) addr = addr - tr.max_addr + tr.addr;
   end
   tr.status = vmm_rw::IS_OK;
endtask: execute_burst


task vmm_rw_xactor::main();
   vmm_rw_access tr;
   vmm_rw_burst  br;
   bit is_exec_sng	= 0;

   fork
      super.main();
   join_none

   fork 
			 begin
				  vmm_rw_access obs_tr;
      forever begin
        this.observe_single(obs_tr);
								if(!is_exec_sng) 
 								this.obsv_chan.put(obs_tr);
								is_exec_sng = 'b0;
						end
    end
			join_none

   forever begin
      this.wait_if_stopped_or_empty(this.exec_chan);

`ifdef VMM_RAL_PIPELINED_ACCESS
      this.exec_chan.get(tr);
`else
      this.exec_chan.activate(tr);
      void'(this.exec_chan.start());
`endif

      if ($cast(br, tr)) begin
         `vmm_callback(vmm_rw_xactor_callbacks,
                       pre_burst(this, br));
         this.execute_burst(br);
         `vmm_callback(vmm_rw_xactor_callbacks,
                       post_burst(this, br));
         this.notify.indicate(BURST_DONE, br);
      end
      else begin
         `vmm_callback(vmm_rw_xactor_callbacks, pre_single(this, tr));
									is_exec_sng = 'b1;
         this.execute_single(tr);
`ifdef VMM_RAL_PIPELINED_ACCESS
         if (tr.status == vmm_rw::PENDING) begin
            fork
               vmm_rw_access rw = tr;
               begin
                  rw.notify.wait_for(vmm_data::ENDED);
                  `vmm_callback(vmm_rw_xactor_callbacks,
                                post_single(this, rw));
                  this.notify.indicate(SINGLE_DONE, rw);
               end
            join_none
         end
`else
         `vmm_callback(vmm_rw_xactor_callbacks,
                       post_single(this, tr));
         this.notify.indicate(SINGLE_DONE, tr);
`endif
      end

`ifndef VMM_RAL_PIPELINED_ACCESS
      void'(this.exec_chan.complete());
      void'(this.exec_chan.remove());
`endif
   end
endtask: main


function void vmm_rw_xactor::reset_xactor(vmm_xactor::reset_e rst_typ= vmm_xactor::SOFT_RST);
   vmm_rw_access tr;

   super.reset_xactor(rst_typ);

   // Force a completion of the transaction to avoid
   // leaving the RAL model blocked
   tr = this.exec_chan.active_slot();
   if (tr != null) begin
      tr.status = vmm_rw::RETRY;
      void'(this.exec_chan.complete());
      void'(this.exec_chan.remove());
   end
   this.exec_chan.flush();
endfunction: reset_xactor

function bit vmm_rw_xactor::supports_byte_enable();
   return 0;
endfunction: supports_byte_enable


