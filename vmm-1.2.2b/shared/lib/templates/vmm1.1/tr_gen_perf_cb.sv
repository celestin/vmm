//
// Template for VMM-compliant Perf Callbacks
// <TR>   Name of transaction descriptor class
// [filename] TR_gen_perf_cb

`ifndef TR_gen_perf_cb__SV
`define TR_gen_perf_cb__SV

ATMC_GEN_START
class TR_gen_perf_cb extends TR_atomic_gen_callbacks;

   vmm_perf_analyzer perf;
  
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction: new

   virtual task post_inst_gen(TR_atomic_gen gen, TR obj, ref bit drop);
      fork begin
         vmm_perf_tenure gen_tenure = new(gen.stream_id,,obj);

         // ToDo: Replace vmm_data::STARTED with user defined notification if required. 
         obj.notify.wait_for(vmm_data::STARTED);
         this.perf.start_tenure(gen_tenure);

         // ToDo: Replace vmm_data::ENDED with user defined notification if required. 
         obj.notify.wait_for(vmm_data::ENDED);
         this.perf.end_tenure(gen_tenure);

      end join_none
   endtask: post_inst_gen

endclass: TR_gen_perf_cb
ATMC_GEN_END
SCN_GEN_START

class TR_gen_perf_cb extends TR_scenario_gen_callbacks;

   vmm_perf_analyzer perf;
 
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction: new

   virtual task post_inst_gen(TR_scenario_gen, TR_scenario tr, ref bit dropped);
     TR trans;
     foreach(tr.items[i])
      begin
        trans = new();
        $cast(trans,tr.items[i].copy());
        fork begin
           vmm_perf_tenure gen_tenure = new(gen.stream_id,,trans);
           // ToDo: Replace vmm_data::STARTED with user defined notification if required. 

           trans.notify.wait_for(vmm_data::STARTED);
           this.perf.start_tenure(gen_tenure);
           // ToDo: Replace vmm_data::ENDED with user defined notification if required. 

           trans.notify.wait_for(vmm_data::ENDED);
           this.perf.end_tenure(gen_tenure);
        end join_none
     end 
   endtask: post_inst_gen

endclass: TR_gen_perf_cb
SCN_GEN_END
GNRC_DRIV_START

class TR_gen_perf_cb extends vmm_ms_scenario_gen_callbacks;
 
   vmm_perf_analyzer perf;
 
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction: new

   // ToDo: Add additional relevant callbacks

   // Called after the transaction is generated by the generator
   virtual task post_scenario_gen(vmm_ms_scenario_gen gen,vmm_ms_scenario tr,ref bit dropped);
      //ToDo : Add logic for starting and ending the performance tenures 

   endtask: post_scenario_gen

endclass:  TR_gen_perf_cb
GNRC_DRIV_END

`endif // TR_gen_perf_cb__SV

