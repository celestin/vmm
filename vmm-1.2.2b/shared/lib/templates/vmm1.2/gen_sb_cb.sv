//
// Template for VMM-compliant Data Stream Scoreboard Callbacks
// <SB>         Name of VMM Scoreboard Class
// <TR>         Name of transaction descriptor class
// [filename]   TR_gen_sb_cb

`ifndef TR_gen_sb_cb__SV
`define TR_gen_sb_cb__SV

`include "TR.sv"
`include "SB.sv"

typedef class SB;
ATMC_GEN_START


typedef class TR_atomic_gen;

class TR_gen_sb_cb extends TR_atomic_gen_callbacks;

   `vmm_typename(TR_gen_sb_cb)
   vmm_tlm_analysis_port #(TR_gen_sb_cb,TR) gen_analysis_port;  //Instance of Generator's analysis port


   function new();
      gen_analysis_port= new(this,"Gen-Sb analysis port"); 
   endfunction: new
   // ToDo: Add additional relevant callbacks


   // Called after the transaction is generated by the generator
   virtual task post_inst_gen(TR_atomic_gen gen, TR tr, ref bit drop);
      gen_analysis_port.write(tr);
      // ToDo: Add relevant code if required 

   endtask: post_inst_gen

endclass:  TR_gen_sb_cb
ATMC_GEN_END
SCN_GEN_START


typedef class TR_scenario_gen;

class TR_gen_sb_cb extends TR_scenario_gen_callbacks;

   `vmm_typename(TR_gen_sb_cb)
   vmm_tlm_analysis_port #(TR_gen_sb_cb,TR) gen_analysis_port;  //Instance of Generator's analysis port

   function new();
      gen_analysis_port= new(this,"Gen-Sb analysis port"); 
   endfunction: new
   // ToDo: Add additional relevant callbacks


   // Called after the transaction is generated by the generator
   virtual task post_scenario_gen(TR_scenario_gen gen,TR_scenario tr,ref bit dropped);
      TR trans;
      foreach(tr.items[i])
      begin
        trans = new();
        $cast(trans,tr.items[i].copy());
        gen_analysis_port.write(trans);
      end
      // ToDo: Add relevant code if required 

   endtask: post_scenario_gen

endclass:  TR_gen_sb_cb
SCN_GEN_END
GNRC_DRIV_START


class TR_gen_sb_cb extends vmm_ms_scenario_gen_callbacks;

   `vmm_typename(TR_gen_sb_cb)
   vmm_tlm_analysis_port #(TR_gen_sb_cb,TR) gen_analysis_port;  //Instance of Generator's analysis port

   function new();
      gen_analysis_port= new(this,"Gen-Sb analysis port"); 
   endfunction: new
   // ToDo: Add additional relevant callbacks


   // Called after the transaction is generated by the generator
   virtual task post_scenario_gen(vmm_ms_scenario_gen gen,vmm_ms_scenario tr,ref bit dropped);
      //ToDo : Add logic to pass the data to the scoreboard using gen_analysis_port.write

   endtask: post_scenario_gen

endclass:  TR_gen_sb_cb
GNRC_DRIV_END

`endif // TR_gen_sb_cb__SV