typedef class sram_model;

class sram_model_callbacks extends vmm_xactor_callbacks;
   // Lab 2c - Create 2 callback methods pre_trans() and post_trans()
   virtual task pre_trans(sram_model bfm, sram_trans tr, ref bit drop); endtask
   virtual task post_trans(sram_model bfm, sram_trans tr); endtask
endclass

class sram_model extends vmm_xactor;
   `vmm_typename(sram_model)
   virtual sram_if.memprt  sigs;
   logic [7:0]             memQ[int];
   string                  resp_kind;
   bit [7:0]               start_addr, end_addr;

   extern function new(string inst, vmm_unit parent=null, int port_id);
   extern virtual function void configure_ph();
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual protected task main();
endclass

function sram_model::new(string inst, vmm_unit parent=null, int port_id);
   super.new(get_typename(), inst, port_id, parent);
endfunction

task sram_model::main();
   int tr_count = 0;
   sram_trans tr = new();
   super.main();

   sigs.ramData <= 'z;
   tr.stream_id = this.stream_id;

   while (1) begin : w0
      bit [31:0] addr;

      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      this.notify.reset(vmm_xactor::XACTOR_BUSY);
      @(negedge(sigs.ce_N));
      this.notify.reset(vmm_xactor::XACTOR_IDLE);
      this.notify.indicate(vmm_xactor::XACTOR_BUSY);

      addr = sigs.ramAddr;
      tr.address = addr;
      tr.data_id = tr_count++;

      if (sigs.rdWr_N) begin
         tr.kind = sram_trans::READ;
         if(addr >= start_addr && addr <= end_addr) begin
            if (memQ.exists(addr)) begin
               sigs.ramData = #5 memQ[addr];
               tr.data = memQ[addr];
            end
            else begin
               reg [7:0] data;
               case(resp_kind)
                  "RESP_00"  : data = 0;
                  "RESP_FF"  : data = '1;
                  "RESP_XX"  : data = 'x;
                  "RESP_RAND": data = $urandom();
               endcase
               memQ[addr] = data;
               tr.data = data;
               sigs.ramData = #5 data;
            end
  	    `vmm_trace(log, tr.psdisplay("sram_model received a READ request "));
         end
         @(sigs.cb);
         sigs.ramData = #5 'z;
      end
      else begin
         tr.kind = sram_trans::WRITE;
         memQ[addr] = sigs.ramData;
         tr.data = memQ[addr];
  	 `vmm_trace(log, tr.psdisplay("sram_model received a WRITE request "));
         @(sigs.cb);
      end

      // Lab 2c - insert callback hook post_trans() after WRITE/READ cycle
      `vmm_callback(sram_model_callbacks, post_trans(this, tr));
   end : w0
endtask

function void sram_model::configure_ph();
   `vmm_note(log, $psprintf("sram_model[%0d] - Configurating the sram start and end addresses within the configure_ph()", this.stream_id));
   resp_kind  = "RESP_RAND";
   start_addr = 0;
   end_addr   = '1;
endfunction

function void sram_model::connect_ph();
   `vmm_note(log, $psprintf("sram_model[%0d] - Connecting the sram_model to the DUT within the connect_ph()", this.stream_id)); 
   this.sigs = sram_port[stream_id].sigs;
endfunction

function void sram_model::start_of_sim_ph();
   if (sigs == null)
      `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction

