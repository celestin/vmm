//
// Template for VMM-compliant generic master component
// <XACT>       Name of generic driver xactor
// <TR>         Name of transaction descriptor
// <IF>         Name of the interface
// <SB>         Name of scoreboard
//

`ifndef XACT__SV
`define XACT__SV

`include "XACT_base.sv"

typedef class SB;
    
class XACT_sb_cb extends XACT_base_cb #(TR);
   SB sb;
 
   function new(SB sb);
      this.sb = sb;

   endfunction: new 


   virtual task pre_send(TR obj); 

      // ToDo: Scoreboard tasks to be done before sending transactions.

   endtask: pre_send


   virtual task post_send(TR obj);
      
      // ToDo: Scoreboard tasks to be done after sending transactions.

   endtask: post_send

endclass: XACT_sb_cb


class XACT_cov_cb extends XACT_base_cb #(TR);

   // ToDo: Add cover groups here
   
   function new();
      // ToDo: Instantiate cover groups
   
   endfunction:  new


   virtual task pre_send(TR obj); 

      // ToDo: Coverage tasks to be done before sending transactions.

   endtask: pre_send


   virtual task post_send(TR obj);
      
      // ToDo: Coverage tasks to be done after sending transactions.

   endtask: post_send

endclass: XACT_cov_cb

PERF_START
class XACT_perf_cb extends vmm_xactor_callbacks;

   vmm_perf_analyzer perf;
  
   function new(vmm_perf_analyzer perf);
      this.perf = perf;
   endfunction:new

   // ToDo: Add required parametes in post_send
   virtual task post_send();
      fork begin
         vmm_perf_tenure driver_tenure = new();

         // ToDo: Add tenure start notification in wait_for(). 
         //Example:obj.notify.wait_for(. . .);

         this.perf.start_tenure(driver_tenure);

         // ToDo: Add tenure start notification in wait_for().
         //Example:obj.notify.wait_for(. . .);
   
         this.perf.end_tenure(driver_tenure);

      end join_none
   endtask: post_send

endclass: XACT_perf_cb
PERF_END

class XACT extends XACT_base #(TR, TR_scenario);
  
   virtual IF intf_i;
   
   MACRO_START
   `vmm_xactor_member_begin(XACT)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(XACT)
   // ToDo: Add required short hand override method
   MACRO_END

   extern function new(string inst = "master", 
                       int stream_id = -1, 
                       virtual IF intf_i);
   extern task send(TR pkt2send);
   extern task execute_mss(ref TR_scenario scn);

endclass: XACT


function XACT::new(string inst = "master", 
                   int stream_id = -1, 
                   virtual IF intf_i);

   super.new("Driver", inst, stream_id);

endfunction: new 


task XACT::send(TR pkt2send);
   // ToDo: Add driving logic here

endtask: send


task XACT::execute_mss(ref TR_scenario scn);
   // ToDo: Radomize scenario here

endtask: execute_mss
 
`endif // XACT__SV
