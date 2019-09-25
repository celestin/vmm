//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

`ifndef NO_VMM12_PARAM_CHANNEL
typedef class vmm_atomic_gen;

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_atomic_gen_callbacks #(type T = `VMM_DATA, C=vmm_channel_typed#(T), string text = "") extends vmm_xactor_callbacks; 
   virtual task post_inst_gen (vmm_atomic_gen #(T,C,text)   gen, 
                             T                   obj, 
                             ref bit             drop); 
   endtask 
endclass 
`endif //NO_VMM12_PARAM_CHANNEL

`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
class vmm_atomic_gen_base extends `VMM_XACTOR;
     function new(string name,
                  string       inst, 
                int          stream_id = -1
                 `VMM12_XACTOR_NEW_ARGS `VMM_XACTOR_NEW_ARGS); 
      super.new(name, inst, stream_id `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL);  
     endfunction

     virtual function void Xset_blueprintX(vmm_data tr);
     endfunction

endclass

`ifndef NO_VMM12_PARAM_CHANNEL
`ifdef VCS
(* _vcs_vmm_class  = 1 *)
`endif
//////////////////////////////////////////////
// Class: vmm_atomic_gen#(T)
//
//    This class implements a parameterized atomic generator. This generator 
// can generate non-vmm_data transactions as well.
//
//    A macro is used to define a class named class-name_atomic_gen for any user-specified 
// class derived from vmm_data, using a process similar to the <vmm_channel> macro.
//    The atomic generator class is an extension of the vmm_xactor class and as such, 
// inherits all the public interface elements provided in the base class.
//
//|   class ahb_trans extends vmm_data;
//|      rand bit [31:0] addr;
//|      rand bit [31:0] data;
//|   endclass
//|
//|   `vmm_channel(ahb_trans)
//|   `vmm_atomic_gen(ahb_trans, "AHB Atomic Gen")
//|   ahb_trans_channel chan0 = new("ahb_trans_chan", "chan0");
//|   ahb_trans_atomic_gen   gen0  = new("AhbGen0", 0, chan0);
//|
//|   Is the same as:
//|   vmm_channel_typed #(ahb_trans) chan0 = new("ahbchan",
//|      "chan0");
//|   vmm_atomic_gen #(ahb_trans, , "Atomic Gen") gen0  = new("AhbGen0", 0, chan0);
//////////////////////////////////////////////

class vmm_atomic_gen #(type T = `VMM_DATA, C=vmm_channel_typed#(T), string text = "") extends vmm_atomic_gen_base;
   int unsigned stop_after_n_insts; 
   typedef enum int {GENERATED, DONE} symbols_e; 
 
   T randomized_obj; 
   C out_chan;
 
   local int scenario_count; 
   local int obj_count; 
 
//////////////////////////////////////////////
// Function: new
//
//    Creates a new instance of the class-name_atomic_gen class, with the specified instance name 
// and optional stream identifier. You can optionally connect the generator to the specified 
// output channel. If you did not specify any output channel instance, one will be created 
// internally in the class-name_atomic_gen::out_chan property.
//
//    The name of the transactor is defined as the user-defined class description string specified
//  in the class implementation macro appended with Atomic Generator.
//  The parent argument should be passed if implicit phasing needs to be enabled.
//
//|   `vmm_channel(alu_data)
//|   Class alu_env extends vmm_group;
//|      vmm_atomic_gen#(alu_data, ,"AluGen") gen_a;
//|      alu_data_channel alu_chan;
//|      . . .
//|      function void build_ph();
//|         alu_chan   = new ("ALU", "channel");
//|         gen_a      = new("Gen", 0,alu_chan ,this);
//|      endfunction
//|      . . .
//|   endclass
//////////////////////////////////////////////

   function new(string       inst, 
                int          stream_id = -1, 
                C out_chan  = null `VMM12_XACTOR_NEW_ARGS `VMM_XACTOR_NEW_ARGS); 
      super.new({text, " Atomic Generator"}, inst, stream_id `VMM12_XACTOR_NEW_CALL `VMM_XACTOR_NEW_CALL); 
      if (out_chan == null) begin 
          out_chan = new({text, " Atomic Generator output channel"}, 
                         inst); 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_CHANNEL
      `VMM_OBJECT_SET_PARENT(out_chan, this) 
`endif
`endif
      end 
      this.out_chan = out_chan; 
      this.out_chan.set_producer(this);
      this.log.is_above(this.out_chan.log); 
 
      this.scenario_count = 0; 
      this.obj_count = 0; 
      this.stop_after_n_insts = 0; 
 
      this.notify.configure(GENERATED, vmm_notify::ONE_SHOT); 
      this.notify.configure(DONE, vmm_notify::ON_OFF); 
      this.randomized_obj = new; 
`ifdef VMM12_XACTOR_BASE
`ifdef VMM_12_UNDERPIN_VMM_DATA
      `VMM_OBJECT_SET_PARENT(randomized_obj, this) 
`endif
`endif
   endfunction: new 
 
   virtual function void Xset_blueprintX(vmm_data tr);
      if (!$cast(randomized_obj, tr)) begin
         `vmm_trace(log, "Type mismatch!! Unable to set the blueprint object to randomized_obj");
      end
   endfunction

//////////////////////////////////////////////
// Task: inject
//
// You can use this method to inject directed stimulus, while the generator is running 
// (with unpredictable timing) or when the generator is stopped.
// Unlike injecting the descriptor directly in the output channel, it counts toward 
// the number of instances generated by this generator and will be subjected to the 
// callback methods. The method returns once the instance is consumed by the output 
// channel or it is dropped by the callback methods.
//
//|
//|   task directed_stimulus;
//|     eth_frame to_phy, to_mac;
//|     ...
//|     to_phy = new;
//|     to_phy.randomize();
//|     ...
//|     fork
//|       env.host_src.inject(to_phy, dropped);
//|       begin
//|         // Force the earliest possible collision
//|         @ (posedge tb_top.mii.tx_en);
//|         env.phy_src.inject(to_mac, dropped);
//|       end
//|     join
//|     ...
//|     -> env.end_test;
//|   endtask: directed_stimulus
//////////////////////////////////////////////

   virtual task inject(T obj, 
                       ref bit    dropped); 
      dropped = 0; 
 
      `vmm_callback(vmm_atomic_gen_callbacks#(T,C,text),post_inst_gen(this, obj, dropped)); 
 
      if (!dropped) begin 
         this.obj_count++; 
         out_chan.wait_for_request();
         this.notify.indicate(GENERATED, obj); 
         this.out_chan.put(obj); 
      end 
   endtask: inject 
 
   virtual function void reset_xactor(vmm_xactor::reset_e rst_type = SOFT_RST); 
      super.reset_xactor(rst_type); 
 
      this.out_chan.flush(); 
      this.scenario_count = 0; 
      this.obj_count = 0; 
 
      if (rst_type >= FIRM_RST) begin 
         this.notify.reset( , vmm_notify::HARD); 
      end 
 
      if (rst_type >= HARD_RST) begin 
         this.stop_after_n_insts = 0; 
         this.randomized_obj     = new; 
      end 
   endfunction: reset_xactor 
 
   virtual function void start_xactor();
`ifdef VMM12_XACTOR_BASE
      `vmm_unit_config_int(stop_after_n_insts, stop_after_n_insts, "runs number of instances", 0, DO_ALL)
`endif
      super.start_xactor();
   endfunction

   virtual protected task main(); 
      bit dropped; 
 
      fork 
         super.main(); 
      join_none 
 
      while (this.stop_after_n_insts <= 0 || 
             this.obj_count < this.stop_after_n_insts) begin 
 
         this.wait_if_stopped(); 
 
         this.randomized_obj.stream_id   = this.stream_id; 
         this.randomized_obj.scenario_id = this.scenario_count; 
         this.randomized_obj.data_id     = this.obj_count; 
 
         if (!this.randomized_obj.randomize()) begin 
            `vmm_fatal(this.log, "Cannot randomize atomic instance"); 
            continue; 
         end 
 
         begin 
            T obj; 
 
            $cast(obj, this.randomized_obj.copy()); 
            this.inject(obj, dropped); 
         end 
      end 
 
      this.notify.indicate(DONE); 
      this.notify.indicate(XACTOR_STOPPED); 
      this.notify.indicate(XACTOR_IDLE); 
      this.notify.reset(XACTOR_BUSY); 
      this.scenario_count++; 
   endtask: main 
 
endclass

`endif // NO_VMM12_PARAM_CHANNEL
