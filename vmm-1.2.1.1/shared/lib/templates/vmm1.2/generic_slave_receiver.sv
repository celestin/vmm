//
// Template for VMM-compliant generic slave receiver component
// <REC>       Name of generic receiver component 
// <IF>        Name of physical interface
// <TR>        Name of input/output transaction descriptor class
// <PRT>       Name of the interface wrapper object
//

`ifndef REC__SV
`define REC__SV

`include "REC_base.sv"

typedef class REC;

class REC_cov_cb extends REC_base_cb #(TR);

   `vmm_typename(REC_cov_cb)
   // ToDo: define covergroups 


   function new();
      // ToDo: instantiate covergroups  

   endfunction: new


   virtual task pre_recv(TR tr); 
      // ToDo: Coverage tasks to be done before receiving transactions.

   endtask: pre_recv


   virtual task post_recv(TR tr);
      // ToDo: Coverage tasks to be done after receiving transactions.
 
   endtask: post_recv

endclass: REC_cov_cb


class REC extends REC_base #(TR);

   `vmm_typename(REC)
   virtual IF.slave intf_i;
   PRT        iport_obj;
   RTLCFG_START
   REC_config rtl_cfg;  //Instance of RTL config
   RTLCFG_END

   MACRO_START
   `vmm_xactor_member_begin(REC)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(REC)
      // ToDo: Add required short hand override method
   MACRO_END 


   extern function new(string name = "REC",
                       string inst = "", 
                       int    stream_id = -1, 
                       TR_channel out_chan = null,
                       vmm_object parent = null
                       ); 
   extern virtual task receive (ref TR pkt);
	XCT_EXPL_START
	extern virtual function void connect();
	XCT_EXPL_END
   XCT_IMPL_START
   RTLCFG_START 
   extern virtual function void configure_ph();
   RTLCFG_END
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task start_ph();
   XCT_IMPL_END
   
endclass: REC


function REC::new(string name = "REC",
                  string inst = "", 
                  int stream_id = -1,
                  TR_channel out_chan = null,
                  vmm_object parent = null
                  );
   super.new("Receiver", inst, stream_id, out_chan, parent);
   XCT_EXPL_START
   this.intf_i = intf_i; 
   XCT_EXPL_END
endfunction: new
XCT_IMPL_START
RTLCFG_START


function void REC::configure_ph();
   $cast(rtl_cfg, vmm_rtl_config::get_config(this, `__FILE__, `__LINE__));
   if (rtl_cfg == null) begin
      `vmm_error(log, `vmm_sformatf("null Config obtained for %s", this.get_object_hiername()));
      return;
   end
endfunction: configure_ph
RTLCFG_END
XCT_IMPL_END
XCT_EXPL_START


function void REC::connect();
XCT_EXPL_END
XCT_IMPL_START


function void REC::connect_ph();
XCT_IMPL_END
   bit is_set;
   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"rec_port"))) begin
      if (iport_obj != null)
         this.intf_i = iport_obj.iport_slv;
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


function void REC::start_of_sim_ph();
   if (intf_i == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction: start_of_sim_ph


task REC::start_ph();
   super.start_ph();
endtask: start_ph
XCT_IMPL_END


task REC::receive(ref TR pkt);
    // ToDo: Add receiver specific logic
    `vmm_note(log, "Add receiver specific logic which can NEW the transaction pkt of type TR");
    `vmm_note(log, "User need to remove $finish once receiver specific logic is added");
    $finish;
endtask: receive

`endif // REC__SV
