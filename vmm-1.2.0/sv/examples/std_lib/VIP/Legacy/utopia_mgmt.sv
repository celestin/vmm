//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

class utopia_mgmt_tr extends vmm_data;

   static vmm_log log = new("utopia_mgmt_tr", "class");

   typedef enum {READ, WRITE} kind_e;
   rand kind_e kind;

   rand bit [11:0] addr;
   rand bit [ 7:0] data;

   function new();
      super.new(this.log);
   endfunction: new

   virtual function string psdisplay(string prefix = "");
      $sformat(psdisplay, "%s#%0d.%0d.%0d %s @ 12'h%h = 8'h%h", prefix,
               this.stream_id, this.scenario_id, this.data_id,
               (this.kind == READ) ? "READ" : "WRITE",
               this.addr, this.data);
   endfunction: psdisplay

   virtual function bit is_valid(bit silent = 1,
                                 int kind   = -1);
     is_valid = 1;
   endfunction: is_valid

   virtual function vmm_data allocate();
      utopia_mgmt_tr tr = new;
      allocate = tr;
   endfunction: allocate

   virtual function vmm_data copy(vmm_data cpy = null);
      utopia_mgmt_tr tr;

      if (cpy == null) tr = new;
      else if (!$cast(tr, cpy)) begin
         `vmm_fatal(this.log, "Attempting to copy to a non-utopia_mgmt_tr instance");
         return null;
      end

      this.copy_data(tr);
      tr.kind = this.kind;
      tr.addr = this.addr;
      tr.data = this.data;

   endfunction: copy
   
   virtual function bit compare(       vmm_data to,
                                output string   diff,
                                input  int      kind = -1);
      utopia_mgmt_tr tr;

      compare = 0;

      if (to == null || !$cast(tr, to)) begin
         `vmm_fatal(this.log, "Attempting to compare to a non-utopia_mgmt_tr instance");
         return 0;
      end

      if (this.kind != tr.kind) begin
         diff = "Transaction kinds are different";
         return 0;
      end
      if (this.addr != tr.addr) begin
         diff = "Transaction addresses are different";
         return 0;
      end
      if (this.data != tr.data) begin
         diff = "Transaction data are different";
         return 0;
      end

      compare = 1;

   endfunction: compare
   
endclass: utopia_mgmt_tr
`vmm_channel(utopia_mgmt_tr)
`vmm_atomic_gen(utopia_mgmt_tr, "Utopia Management Transaction")

   
class utopia_mgmt_cfg;
   rand bit is_intel;
endclass: utopia_mgmt_cfg


class utopia_mgmt extends vmm_xactor;
   utopia_mgmt_cfg cfg;
   utopia_mgmt_tr_channel in_chan;

// Example 4-93
   function new(
`ifndef ONLY_ONE_INSTANCE
                string                 inst,
                integer                stream_id = -1,
`endif
                utopia_mgmt_tr_channel in_chan = null);
`ifdef ONLY_ONE_INSTANCE
      super.new("Utopia Mgmt", "top.mgmt", stream_id);
`else
      super.new("Utopia Mgmt", inst, stream_id);
`endif

      if (in_chan == null) begin
         in_chan = new("Utopia Mgmt Input Channel", this.get_instance());
         this.log.is_above(in_chan.log);
      end
      this.in_chan = in_chan;

      this.cfg = new;
`ifdef ONLY_ONE_INSTANCE
      this.cfg.is_intel = top.mgmt.BusMode;
`endif
   endfunction: new

   virtual task read(input  [11:0] radd,
                     output [ 7:0] rdat);
      `vmm_fatal(this.log, "Not associated with a module instance");
      rdat = 8'hXX;
   endtask

   virtual task write(input [11:0] radd,
                      input [ 7:0] rdat);
      `vmm_fatal(this.log, "Not associated with a module instance");
   endtask
 
   virtual task main();
      fork
         super.main();
      join_none

      forever begin
         utopia_mgmt_tr tr;

         this.wait_if_stopped_or_empty(this.in_chan);
         this.in_chan.activate(tr);
         void'(this.in_chan.start());

         case (tr.kind)
            utopia_mgmt_tr::READ :  this.read(tr.addr, tr.data);
            utopia_mgmt_tr::WRITE: this.write(tr.addr, tr.data);
         endcase

         void'(this.in_chan.complete());
         void'(this.in_chan.remove());
      end
   endtask: main

endclass: utopia_mgmt


// Example 4-94
// Example 4-95
`ifndef ONLY_ONE_INSTANCE
`define utopia_mgmt(path) \
class \path.utopia_mgmt extends utopia_mgmt; \
 \
   function new(integer                stream_id = -1, \
                utopia_mgmt_tr_channel in_chan = null); \
      super.new("path", stream_id, in_chan); \
      super.cfg.is_intel = path.BusMode; \
   endfunction: new \
 \
   virtual task read(input  [11:0] radd, \
                     output [ 7:0] rdat); \
      path.read(radd, rdat); \
   endtask: read \
 \
   virtual task write(input [11:0] wadd, \
                      input [ 7:0] wdat); \
      path.write(wadd, wdat); \
   endtask: write \
endclass
`endif
