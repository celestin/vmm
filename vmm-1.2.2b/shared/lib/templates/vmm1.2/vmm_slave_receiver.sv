//
// Template for VMM-compliant slave receiver
//  <REC>       Name of slave receiver for generic receiver base component
//

`ifndef REC_base__SV
`define REC_base__SV


class REC_base_cb #(type T = vmm_data) extends vmm_xactor_callbacks;

   `vmm_typename(REC_base_cb)
   //Called before receiving transactions.
   virtual task pre_recv(T obj);
   
   endtask: pre_recv
   

   //Called after receiving transactions.
   virtual task post_recv(T obj); 
   
   endtask: post_recv 

endclass: REC_base_cb


class REC_base #(type T=vmm_data) extends vmm_xactor;

   `vmm_typename(REC_base)
   T obj;
   vmm_channel_typed #(T) chan;
   MACRO_START
   `vmm_xactor_member_begin(REC_base)
      `vmm_xactor_member_vmm_data(obj,DO_ALL)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(REC_base)
   MACRO_END
   // ToDo: Add required short hand override method

   
   extern function new(string name = "Receiver_base", 
                       string inst = "", 
                       int stream_id = -1, 
                       vmm_channel_typed #(T) chan = null,
		                   vmm_object parent = null);
   extern virtual task receive(ref T obj);
   XCT_EXPL_START
   extern virtual task main();
   XCT_EXPL_END
   XCT_IMPL_START
   extern virtual task start_ph();
   XCT_IMPL_END

endclass: REC_base


function REC_base::new(string name = "Receiver_base",
                       string inst = "", 
                       int stream_id = -1, 
                       vmm_channel_typed #(T) chan = null,
		                   vmm_object parent = null);
   super.new(name, inst, stream_id, parent);
   `vmm_debug(this.log, $psprintf("%m"));
   if (chan == null)
      chan = new($psprintf("%s channel", name), inst);
   this.chan = chan;
   this.chan.set_parent(this);
   this.stream_id = stream_id;
	this.set_parent(parent);
endfunction: new
XCT_EXPL_START


task REC_base::main();
   super.main();
XCT_EXPL_END
XCT_IMPL_START


task REC_base::start_ph();
   super.start_ph();
XCT_IMPL_END
   `vmm_debug(this.log, $psprintf("%m"));
   forever begin
      T obj;
      this.notify.reset(vmm_xactor::XACTOR_IDLE);
      `vmm_callback(REC_base_cb #(T), pre_recv(obj));
      receive(obj);
      `vmm_trace(this.log, obj.psdisplay("receive() "));
      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      `vmm_callback(REC_base_cb #(T), post_recv(obj));
      chan.put(obj.copy());
   end
XCT_EXPL_START
endtask : main
XCT_EXPL_END
XCT_IMPL_START
endtask: start_ph 
XCT_IMPL_END


task REC_base::receive(ref T obj);
   // ToDo: Add valid code for generating received transaction.

endtask: receive

`endif // REC_base__SV
