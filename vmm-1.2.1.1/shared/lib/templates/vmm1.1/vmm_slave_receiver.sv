//
// Template for VMM-compliant slave receiver
//  <REC>       Name of slave receiver for generic receiver base component
//

`ifndef REC_base__SV
`define REC_base__SV


class REC_base_cb #(type T = vmm_data) extends vmm_xactor_callbacks;

   //Called before receiving transactions.
   virtual task pre_recv(T obj);
   
   endtask: pre_recv
   

   //Called after receiving transactions.
   virtual task post_recv(T obj); 
   
   endtask: post_recv 

endclass: REC_base_cb


class REC_base #(type T=vmm_data) extends vmm_xactor;
   T obj;
   vmm_channel_typed #(T) chan;
   
   MACRO_START
   `vmm_xactor_member_begin(REC_base)
      `vmm_xactor_member_vmm_data(obj,DO_ALL)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(REC_base)
   MACRO_END
   // ToDo: Add required short hand override method

   extern function new(string name = "", 
                       string inst = "", 
                       int stream_id = -1, 
                       vmm_channel_typed #(T) chan = null);
   extern virtual protected task main();
   extern virtual task receive(ref T obj);

endclass: REC_base


function REC_base::new(string name = "",
                           string inst = "", 
                           int stream_id = -1, 
                           vmm_channel_typed #(T) chan = null);

   super.new("Receiver", inst);
   `vmm_debug(this.log, $psprintf("%m"));
   if (chan == null)
      chan = new($psprintf("%s channel", name), inst);
   this.chan = chan;
   //this.chan.set_parent(this);
   this.stream_id = stream_id;

endfunction: new


task REC_base::main();
   super.main();
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

endtask: main


task REC_base::receive(ref T obj);
   // ToDo: Add valid code for generating received transaction.

endtask: receive

`endif // REC_base__SV
