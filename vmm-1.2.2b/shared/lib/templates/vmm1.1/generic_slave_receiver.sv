//
// Template for VMM-compliant generic slave receiver component
// <REC>       Name of generic receiver component 
// <IF>        Name of physical interface
// <TR>        Name of input/output transaction descriptor class
//

`ifndef REC__SV
`define REC__SV

`include "REC_base.sv"

typedef class REC;

class REC_cov_cb extends REC_base_cb #(TR);

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


class REC extends REC_base #(TR) ;

   virtual IF intf_i;   
   
   MACRO_START
   `vmm_xactor_member_begin(REC)
      // ToDo: Add vmm xactor member 

   `vmm_xactor_member_end(REC)
    // ToDo: Add required short hand override method
   MACRO_END 

   extern function new(string inst = "", 
                       int    stream_id = -1, 
                       TR_channel out_chan = null, 
                       virtual IF intf_i); 

   extern task receive (ref TR pkt);
   
endclass: REC


function REC::new(string inst = "", 
                  int stream_id = -1, 
                  TR_channel out_chan = null, 
                  virtual IF intf_i); 

   super.new("Receiver", inst, stream_id, out_chan); 
   this.intf_i = intf_i; 

endfunction: new


task REC::receive(ref TR pkt);
    // ToDo: Add receiver specific logic
    `vmm_note(log, "Add receiver specific logic which can NEW the transaction pkt of type TR");
    `vmm_note(log, "User need to remove $finish once receiver specific logic is added");
    $finish;
endtask: receive

`endif // REC__SV
