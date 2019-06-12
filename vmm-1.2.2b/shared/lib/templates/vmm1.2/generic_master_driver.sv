//
// Template for VMM-compliant generic master component
// <XACT>       Name of generic driver xactor
// <TR>         Name of transaction descriptor
// <IF>         Name of the interface
// <SB>         Name of scoreboard
// <PRT>        Name of the interface wrapper object
//

`ifndef XACT__SV
`define XACT__SV

`include "XACT_base.sv"

typedef class SB;
 
class XACT_sb_cb extends XACT_base_cb #(TR);

   `vmm_typename(XACT_sb_cb)
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

   `vmm_typename(XACT_cov_cb)
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

   `vmm_typename(XACT_perf_cb)
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

   `vmm_typename(XACT)
   virtual IF.master intf_i;
   PRT iport_obj;

   MACRO_START
   `vmm_xactor_member_begin(XACT)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(XACT)
   // ToDo: Add required short hand override method
   MACRO_END

   extern function new(string name = "XACT",
                       string inst = "", 
                       int stream_id = -1,
                       vmm_object parent = null
                       );
   extern task send(TR pkt2send);
   extern task execute_mss(ref TR_scenario scn);
	XCT_EXPL_START
	extern virtual function void connect();
	XCT_EXPL_END
   XCT_IMPL_START
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task start_ph();
   XCT_IMPL_END

endclass: XACT


function XACT::new(string name = "XACT", 
                   string inst = "",
                   int stream_id = -1,
                   vmm_object parent = null
                  );
   super.new(name, inst, stream_id, parent);
endfunction: new


XCT_EXPL_START
function void XACT::connect();
XCT_EXPL_END
XCT_IMPL_START
function void XACT::connect_ph();
XCT_IMPL_END
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"drv_port"))) begin
      if (iport_obj != null)
         this.intf_i = iport_obj.iport_mst;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
XCT_EXPL_START
endfunction: connect
XCT_EXPL_END
XCT_IMPL_START
endfunction: connect_ph
XCT_IMPL_END
XCT_IMPL_START


function void XACT::start_of_sim_ph();
   if (intf_i == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction: start_of_sim_ph


task XACT::start_ph();
   super.start_ph();
endtask: start_ph
XCT_IMPL_END


task XACT::send(TR pkt2send);
   // ToDo: Add driving logic here

endtask: send


task XACT::execute_mss(ref TR_scenario scn);
   // ToDo: Radomize scenario here

endtask: execute_mss
 
`endif // XACT__SV

