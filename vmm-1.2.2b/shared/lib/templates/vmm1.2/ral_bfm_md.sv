//
// Template for physical access BFM that can be used by RAL
//
// <XACT>       Name of physical-level transactor
// <TR>         Name of physical-level transaction descriptor class
// <DOM>        Name of domain
// [filename]   XACT_DOM_ral
//

`ifndef XACT_DOM_RAL__SV
`define XACT_DOM_RAL__SV
  `include "XACT.sv"

class XACT_DOM_ral extends vmm_rw_xactor;

   `vmm_typename(XACT_DOM_ral)
   XACT bfm;  

   MACRO_START
   `vmm_xactor_member_begin(XACT_DOM_ral)
      `vmm_xactor_member_xactor(bfm, DO_ALL)
      // ToDo: add properties using macros here

   `vmm_xactor_member_end(XACT_DOM_ral)
   MACRO_END

   extern function new(string name = "XACT_ral",
                       string inst = "",
                       int stream_id = -1,
                       XACT bfm,
                       vmm_rw_access_channel exec_chan = null
                       );
   NORMAL_START
   extern virtual function void start_xactor();
   extern virtual function void stop_xactor();
   extern virtual function void reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
   NORMAL_END
   extern virtual task execute_single(vmm_rw_access tr);

endclass: XACT_DOM_ral


function XACT_DOM_ral::new(string name = "XACT_ral",
                           string inst = "",
                           int stream_id = -1,
                           XACT bfm,
                           vmm_rw_access_channel exec_chan = null
                           );
   super.new("XACT RAL Master for DOM domain", inst, stream_id,exec_chan);
   this.bfm = bfm;
endfunction: new
NORMAL_START


function void XACT_DOM_ral::start_xactor();
   super.start_xactor();
   this.bfm.start_xactor();
endfunction: start_xactor


function void XACT_DOM_ral::stop_xactor();
   super.stop_xactor();
   this.bfm.stop_xactor();
endfunction: stop_xactor


function void XACT_DOM_ral::reset_xactor(vmm_xactor::reset_e rst_typ = vmm_xactor::SOFT_RST);
   super.reset_xactor(rst_typ);
   this.bfm.reset_xactor(rst_typ);
endfunction: reset_xactor
NORMAL_END


task XACT_DOM_ral::execute_single(vmm_rw_access tr);
   TR cyc;
   
   // ToDo: Translate the generic RW into an appropriate RW
   // for the specified domain
   cyc = new;
   if (tr.kind == vmm_rw::WRITE) begin
      // Write cycle
      // ...
   end
   else begin
      // Read cycle
      // ...
   end

   this.bfm.in_chan.put(cyc);

   // ToDo: Send the result of read cycles back to the RAL
   if (tr.kind == vmm_rw::READ) begin
      // tr.data = ...
   end
endtask: execute_single

`endif // XACT_DOM_RAL__SV
