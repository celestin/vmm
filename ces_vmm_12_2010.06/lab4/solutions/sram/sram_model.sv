typedef class sram_model;

class sram_model_callbacks extends vmm_xactor_callbacks;
   virtual task pre_trans(sram_model bfm, sram_trans tr, ref bit drop); endtask
   virtual task post_trans(sram_model bfm, sram_trans tr); endtask
endclass

class sram_model extends vmm_xactor;
   `vmm_typename(sram_model)

   virtual sram_if.memprt  sigs;

   // Lab 4 - Declare an instance of the analysis port
   vmm_tlm_analysis_port #(sram_model, sram_trans) analysis_port;

   sramport                sram_port_obj;
   logic [7:0]             memQ[int];
   string                  resp_kind;
   bit   [7:0]             start_addr, end_addr;

   extern function new(string inst, vmm_unit parent=null, int port_id);
   extern virtual function void build_ph();
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
               logic [7:0] data;
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
  	    `vmm_note(log, tr.psdisplay("sram_model received a READ request "));
         end
         @(sigs.cb);
         sigs.ramData = #5 'z;
      end
      else begin
         tr.kind = sram_trans::WRITE;
         memQ[addr] = sigs.ramData;
         tr.data = memQ[addr];
  	 `vmm_note(log, tr.psdisplay("sram_model received a WRITE request "));
         @(sigs.cb);
      end
      `vmm_callback(sram_model_callbacks, post_trans(this, tr));

      // Lab 4 - Call the analysis_port.write() after the sram recieves a WRITE/READ transaction
      analysis_port.write(tr);   
   end : w0
endtask

function void sram_model::build_ph();
   // Lab 4 - Construct the analysis port object
   analysis_port = new(this, "sram_model_analysis_port");
endfunction

function void sram_model::configure_ph();
   `vmm_note(log, $psprintf("sram_model[%0d] - Configurating the sram start and end addresses within the configure_ph()", this.stream_id));
   resp_kind  = "RESP_RAND";
   start_addr = 0;
   end_addr   = '1;
endfunction

function void sram_model::connect_ph();
   bit is_set;
   `vmm_note(log, "sram_model - Connecting the sram_model to the DUT within the connect_ph()"); 
   // Connect the transactor to the DUT using the virtual port wrapper. Use vmm_opts
   $cast(sram_port_obj, vmm_opts::get_object_obj(is_set, this, "sram_port"));
   if (sram_port_obj != null)
      this.sigs = sram_port_obj.sigs;
   else
      `vmm_fatal(log, "Virtual port wrapper not initialized");
endfunction

function void sram_model::start_of_sim_ph();
   if (sigs == null)
      `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction
