//
// Template for VMM-compliant master driver
// <XACT>       Name of master driver for generic driver base component
// [filename]   XACT_base
//

`ifndef XACT_base__SV
`define XACT_base__SV

typedef class XACT_base;

class XACT_base_cb #(type T = vmm_data) extends vmm_xactor_callbacks;

   `vmm_typename(XACT_base_cb)
   //Called before sending transactions.
   virtual task pre_send(T obj);

   endtask: pre_send


   //Called after sending transactions.
   virtual task post_send(T obj); 
   
   endtask: post_send 

endclass: XACT_base_cb


class vmm_mss_typed #(type T=vmm_data, type S=vmm_data) extends vmm_ms_scenario;
  
   `vmm_typename(vmm_mss_typed#(T,S))
   T obj;
   S scn;
   vmm_channel_typed #(T) in_chan;
   local int id;
   local int msc;
   local int max_length = 10;
   local XACT_base #(T,S) parent;
 
   extern function new(string name = "", 
                       string inst = "", 
                       int stream_id = -1, 
                       vmm_channel_typed #(T) in_chan = null, 
                       XACT_base #(T,S) parent = null);
   extern function set_length(int length);
   extern virtual task execute(ref int n);
  
endclass: vmm_mss_typed


function vmm_mss_typed::new(string name = "", 
                            string inst = "", 
                            int stream_id = -1, 
                            vmm_channel_typed #(T) in_chan = null, 
                            XACT_base #(T,S) parent = null);
   super.new(null);
   this.msc = this.define_scenario({name,inst}, this.max_length);
   this.id = stream_id;
   if(in_chan==null) 
      this.in_chan = new($psprintf("%s MSS Chan", name), inst);
   else
      this.in_chan = in_chan;
   this.scn = new();
   this.scn.define_scenario($psprintf("%s Scn(%s)", name, inst), this.max_length);
   this.parent = parent;
   this.set_parent(parent);
endfunction: new  


function vmm_mss_typed::set_length(int length);
   this.max_length = length;
endfunction: set_length
 
 
task vmm_mss_typed::execute(ref int n);
   int unsigned nn = 0;
   if(this.parent != null) 
      this.parent.execute_mss(this.scn);
   else 
      scn.randomize;
   this.scn.apply(this.in_chan, nn);
   n += nn;
endtask: execute


class XACT_base #(type T=vmm_data, type S=vmm_data) extends vmm_xactor;

   `vmm_typename(XACT_base#(T,S))
   T obj;
   vmm_channel_typed #(T) in_chan;
   vmm_mss_typed #(T,S) mss;
   vmm_ms_scenario_gen gen;
   MACRO_START
   `vmm_xactor_member_begin(XACT_base)
      `vmm_xactor_member_vmm_data(obj,DO_ALL)
      `vmm_xactor_member_xactor(gen,DO_ALL)
      `vmm_xactor_member_channel(in_chan, DO_ALL)
      // ToDo: Add vmm xactor member

   `vmm_xactor_member_end(XACT_base)
   // ToDo: Add required short hand override method
   MACRO_END

   extern function new(string name = "XACT_base", 
                       string inst = "",
                       int stream_id = -1,
							         vmm_object parent = null
							        );
   XCT_EXPL_START
   extern virtual task main();
   XCT_EXPL_END
   XCT_IMPL_START
   extern virtual task start_ph();
   XCT_IMPL_END
   extern virtual task send(T obj);
   extern virtual task execute_mss(ref S scn);
   extern virtual function void set_scenario(S scn);

endclass: XACT_base


function XACT_base::new(string name = "XACT_base",
                        string inst = "",
                        int stream_id = -1,
								        vmm_object parent = null
								      );
   super.new(name, inst, stream_id, parent);
   `vmm_debug(this.log, $psprintf("%m"));
   in_chan = new($psprintf("%s channel", name), inst);
   this.in_chan   = in_chan;
   this.in_chan.set_parent(this);
   this.mss =  new($psprintf("%s mss", name), inst, stream_id, this.in_chan, this);
   this.stream_id = stream_id;
   this.mss.set_parent(this);
   this.gen = new($psprintf("%s mss gen(%s)", name, inst), stream_id);
   this.gen.set_parent(this);
   this.gen.register_ms_scenario($psprintf("TR_scenario%0d", stream_id), this.mss);
endfunction: new


XCT_EXPL_START
task XACT_base::main();
   super.main();
XCT_EXPL_END
XCT_IMPL_START
task XACT_base::start_ph();
   super.start_ph();
XCT_IMPL_END
   gen.start_xactor();
   `vmm_debug(this.log, $psprintf("%m"));
   forever begin
      T obj;
      wait_if_stopped_or_empty(in_chan);
      in_chan.peek(obj);
      `vmm_callback(XACT_base_cb #(T), pre_send(obj));
      this.notify.reset(vmm_xactor::XACTOR_IDLE);
      `vmm_trace(this.log, obj.psdisplay("send() "));
      send(obj);
      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      `vmm_callback(XACT_base_cb #(T), post_send(obj));
      in_chan.get(obj);
   end
XCT_EXPL_START
endtask: main
XCT_EXPL_END
XCT_IMPL_START
endtask:start_ph 
XCT_IMPL_END


task XACT_base::send(T obj);
   // ToDo: Add valid code for sending transaction.
endtask: send


task XACT_base::execute_mss(ref S scn);
   scn.randomize;
endtask: execute_mss


function void XACT_base::set_scenario(S scn);
   this.mss.scn = scn;
endfunction: set_scenario

`endif // XACT_base__SV

