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


`ifndef VMM_SB_DS_SV
`define VMM_SB_DS_SV

typedef class vmm_sb_ds_iter;
typedef class vmm_sb_ds_stream_iter;
typedef class vmm_sb_ds_pkts;


//
// The packet queues, one for each inp->exp stream pair
//
// (Undocumented)
//
class vmm_sb_ds_pkt_stream #(type DATA = vmm_data);
   DATA pkts[$];

   int n_inserted   = 0;
   int n_matched    = 0;
   int n_mismatched = 0;
   int n_dropped    = 0;
   int n_not_found  = 0;
endclass


//
// Packet queues for one expected stream, one per input stream
//
// (Undocumented)
//
class vmm_sb_ds_exp_streams #(type DATA = vmm_data);
   vmm_sb_ds_pkt_stream#(DATA)  pkt_streams[`VMM_AA_INT];
endclass


//
// Top-Level Data-stream scoreboard class
//
typedef class vmm_sb_ds_callbacks;

class vmm_sb_ds_base extends vmm_unit;
   typedef enum {EITHER, INPUT, EXPECT} kind_e;
   typedef enum {IN_ORDER, WITH_LOSSES, OUT_ORDER} ordering_e;
   typedef enum {INSERTED = 999_000, EMPTY, MATCHED, MISMATCHED,
                 DROPPED, NOT_FOUND, ORPHANED} notifications_e;

   function new(string name ="", string inst="", vmm_object parent=null);
      super.new(name, inst, parent);
   endfunction: new

endclass


`ifndef VCS //Simplifying the code to ensure non-VCS simulators can compile it

class vmm_tlm_analysis_export_inp #(type TARGET = vmm_xactor, type DATA = vmm_data ) extends vmm_tlm_analysis_export_base#(DATA); 
   static local vmm_object _obj; 
   local TARGET m_parent; 

   function  new(TARGET parent, string name , int max_binds = 1 , int min_binds = 0); 
      super.new( ($cast(_obj, parent)) ? _obj : null, name, max_binds, min_binds,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); 
      this.m_parent = parent; 
   endfunction : new  

   virtual function void write(int id =-1, DATA trans); 
      if(this.child_export == null) 
         this.m_parent.write_inp(id, trans); 
      else 
         this.child_export.write(id,trans); 
   endfunction : write 
endclass : vmm_tlm_analysis_export_inp 

class vmm_tlm_analysis_export_exp #(type TARGET = vmm_xactor, type DATA = vmm_data ) extends vmm_tlm_analysis_export_base#(DATA); 
   static local vmm_object _obj; 
   local TARGET m_parent; 

   function  new(TARGET parent, string name , int max_binds = 1 , int min_binds = 0); 
      super.new( ($cast(_obj, parent)) ? _obj : null, name, max_binds, min_binds,((parent != null) && $cast(_obj,parent)) ? _obj.get_log() : null); 
      this.m_parent = parent; 
   endfunction : new  

   virtual function void write(int id =-1, DATA trans); 
      if(this.child_export == null) 
         this.m_parent.write_exp(id, trans); 
      else 
         this.child_export.write(id,trans); 
   endfunction : write 
endclass : vmm_tlm_analysis_export_exp 

`endif


class vmm_sb_ds_typed #(type INP = vmm_data , type EXP = INP) extends vmm_sb_ds_base;

   /*local*/ vmm_sb_ds_exp_streams#(EXP) Xexp_streamsX[`VMM_AA_INT];
   /*local*/ string                Xinp_stream_descsX[`VMM_AA_INT];
   /*local*/ string                Xexp_stream_descsX[`VMM_AA_INT];
   /*local*/ bit                   Xdefine_stream_calledX = 0;
   /*local*/ bit                   Xparallel_streamsX     = 0;

   local int n_not_found     = 0;
   local bit insert_recursed = 0;

   local vmm_sb_ds_callbacks#(INP,EXP) callbacks[$];

   vmm_log    log;
   vmm_notify notify;
`ifndef NO_VMM12_TLM

   `ifdef VCS  // Simplifying the code to ensure non-VCS simulators can compile it
   `vmm_tlm_analysis_export(_inp)
   `vmm_tlm_analysis_export(_exp)
   `endif
   
   vmm_tlm_analysis_export_inp#(vmm_sb_ds_typed#(INP,EXP),INP) inp_ap = new(this,"vmm_sb_ds_typed input analysis export",99,0); 
   vmm_tlm_analysis_export_exp#(vmm_sb_ds_typed#(INP,EXP),EXP) exp_ap = new(this,"vmm_sb_ds_typed expect analysis export",99,0);

`endif

   extern function new(string name, string inst="", vmm_object parent=null);

   extern virtual function int stream_id(vmm_data          pkt,
                                         vmm_sb_ds_typed::kind_e kind = EITHER);

   extern virtual function int inp_stream_id(INP pkt);

   extern virtual function int exp_stream_id(EXP pkt);

   extern function void define_stream(int               stream_id,
                                      string            descr = "",
                                      vmm_sb_ds_typed::kind_e kind = EITHER);

   extern virtual function bit insert(vmm_data          pkt,
                                      vmm_sb_ds_typed::kind_e kind          = INPUT,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit inp_insert(INP           pkt,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit exp_insert(EXP           pkt,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit remove(vmm_data          pkt,
                                      vmm_sb_ds_typed::kind_e kind          = INPUT,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit inp_remove(INP           pkt,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit exp_remove(EXP           pkt,
                                      int               exp_stream_id = -1,
                                      int               inp_stream_id = -1);

   extern virtual function bit transform(input  INP in_pkt,
                                         output EXP out_pkts[]);

   extern virtual function bit match(EXP actual,
                                     EXP expected);

   extern virtual function bit quick_compare(EXP actual,
                                             EXP expected);

   extern virtual function bit compare(EXP actual,
                                       EXP expected);

   extern virtual function void write_inp(int id=-1, INP trans);

   extern virtual function void write_exp(int id=-1, EXP trans);



   virtual function EXP expect_in_order(EXP pkt,
                                int      exp_stream_id = -1,
                                int      inp_stream_id = -1,
                                bit      silent = 0);

      vmm_sb_ds_exp_streams#(EXP) exp_streams;
      vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
   
      if(pkt == null)
      begin
        `vmm_error(this.log,"Null vmm_data pointer provided to vmm_sb_ds::expect_in_order");
        return null;
      end

      if (exp_stream_id < 0) begin
         vmm_data tmp_data;
         if($cast(tmp_data,pkt))
            exp_stream_id = this.stream_id(tmp_data, EXPECT);
         else
            exp_stream_id = this.exp_stream_id(pkt);
      end
      if (inp_stream_id < 0) begin
         vmm_data tmp_data;
         if($cast(tmp_data,pkt))
            inp_stream_id = this.stream_id(tmp_data,INPUT);
         else
            inp_stream_id = this.exp_stream_id(pkt); //Check exp_stream_id
      end

      `vmm_debug(this.log, $psprintf("Expecting in-order packet on stream #%0d->#%0d",
                                     inp_stream_id, exp_stream_id));
      `vmm_verbose(this.log, pkt.psdisplay("   "));

      if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
         // Not found because the output stream does not exist!
         vmm_sb_ds_pkts#(EXP) status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

         if (!silent) begin
            this.n_not_found += n;
            `vmm_error(this.log, $psprintf("In-order packet was not found: EXPECT stream #%0d does not exist.", exp_stream_id));
         end
         return null;
      end
      exp_streams = this.Xexp_streamsX[exp_stream_id];

      if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
         // Not found because the input stream does not exist!
         vmm_sb_ds_pkts#(EXP) status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

         if (!silent) begin
            this.n_not_found += n;
            `vmm_error(this.log, $psprintf("In-order packet was not found: stream #%0d->#%0d does not exist.", inp_stream_id, exp_stream_id));
         end
         return null;
      end
      pkt_stream = exp_streams.pkt_streams[inp_stream_id];

      if (pkt_stream.pkts.size() == 0) begin
         // Not found because the packet stream is empty!
         vmm_sb_ds_pkts#(EXP) status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

         if (!silent) begin
            pkt_stream.n_not_found += n;
            `vmm_error(this.log, $psprintf("In-order packet was not found: stream %0d->%0d is empty.", inp_stream_id, exp_stream_id));
         end
         return null;
      end      

      if (!this.compare(pkt, pkt_stream.pkts[0])) begin
         // Not found because the packet does not match
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

         if (!silent) begin
            pkt_stream.n_not_found += n;
            `vmm_error(this.log, $psprintf("In-order packet was not expected:\n%s\n%s.", pkt.psdisplay("   Actual: "), pkt_stream.pkts[0].psdisplay("   Expect: ")));
         end

         // Remove the packet
         void'(pkt_stream.pkts.pop_front());
         if (pkt_stream.pkts.size() == 0) begin
            // The entire scoreboard might be empty!
            if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
         end

         return null;
      end      

      // Found!
      begin
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         this.notify.indicate(MATCHED, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          matched_internal(this, pkt, exp_stream_id, inp_stream_id, n));
         if (!silent) pkt_stream.n_matched += n;
      end

      pkt = pkt_stream.pkts.pop_front();
      if (pkt_stream.pkts.size() == 0) begin
         // The entire scoreboard might be empty!
         if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
      end

      return pkt;

   endfunction: expect_in_order

   extern virtual function bit expect_with_losses(input  EXP pkt,
                                                output EXP matched,
                                                output EXP lost[],
                                                input  int      exp_stream_id = -1,
                                                input  int      inp_stream_id = -1,
                                                input  bit      silent        = 0);

   virtual function EXP expect_out_of_order(EXP pkt,
                                                    int      exp_stream_id = -1,
                                                    int      inp_stream_id = -1,
                                                    bit      silent = 0);
      vmm_sb_ds_exp_streams#(EXP) exp_streams;
      vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
      int                   match_idx;
   
      if(pkt == null)
      begin
        `vmm_error(this.log,"Null vmm_data pointer provided to vmm_sb_ds::expect_out_of_order");
        return null;
      end
   
      if (inp_stream_id < 0) begin
         vmm_data tmp_data;
         if($cast(tmp_data,pkt))
            inp_stream_id = this.stream_id(tmp_data,INPUT);
         else
            inp_stream_id = this.exp_stream_id(pkt); //TODO check exp_stream_id
      end
      if (exp_stream_id < 0) begin
         vmm_data tmp_data;
         if($cast(tmp_data,pkt))
            exp_stream_id = this.stream_id(tmp_data,EXPECT);
         else
            exp_stream_id = this.exp_stream_id(pkt);
      end
   
      `vmm_debug(this.log, $psprintf("Looking for out-of-order packet on stream #%0d->#%0d",
                                     inp_stream_id, exp_stream_id));
      `vmm_verbose(this.log, pkt.psdisplay("   "));
   
      if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
         // Not found because the output stream does not exist!
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;
   
         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));
   
         if (!silent) begin
            this.n_not_found += n;
            `vmm_error(this.log, $psprintf("Out-of-order packet was not found: EXPECT stream #%0d does not exist.", exp_stream_id));
         end
         return null;
      end
      exp_streams = this.Xexp_streamsX[exp_stream_id];
   
      if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
         // Not found because the input stream does not exist!
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;
   
         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));
   
         if (!silent) begin
            this.n_not_found += n;
            `vmm_error(this.log, $psprintf("Out-of-order packet was not found: stream %0d->%0d does not exist.", inp_stream_id, exp_stream_id));
         end
         return null;
      end
      pkt_stream = exp_streams.pkt_streams[inp_stream_id];
   
      if (pkt_stream.pkts.size() == 0) begin
         // Not found because the packet stream is empty!
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;
   
         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));
   
         if (!silent) begin
            pkt_stream.n_not_found += n;
            `vmm_error(this.log, $psprintf("Out-of-order packet was not found: stream %0d->%0d is empty.", inp_stream_id, exp_stream_id));
         end
         return null;
      end      
   
      foreach (pkt_stream.pkts[i]) begin
         if (this.compare(pkt, pkt_stream.pkts[i])) begin
            // We have a match!
            begin
               vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
               int n = 1;
   
               this.notify.indicate(MATCHED, status);
               `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                                matched_internal(this, pkt, exp_stream_id, inp_stream_id, n));
               if (!silent) pkt_stream.n_matched += n;
            end
   
            pkt = pkt_stream.pkts[i];
            pkt_stream.pkts.delete(i);
            if (pkt_stream.pkts.size() == 0) begin
               // The entire scoreboard might be empty!
               if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
            end
            return pkt;
         end
      end
   
      begin
         vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;
   
         this.notify.indicate(NOT_FOUND, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));
         if (!silent) pkt_stream.n_not_found += n;
      end
   
      if (!silent) begin
         `vmm_error(this.log, "Out-of-order packet was not found");
      end
      return null;
   endfunction: expect_out_of_order

   extern virtual function void flush();

   function vmm_sb_ds_iter#(INP,EXP) new_sb_iter(int exp_stream_id = -1,
                                               int inp_stream_id = -1);

      vmm_sb_ds_iter#(INP,EXP) iter = new(this, exp_stream_id, inp_stream_id);

      return iter;
   endfunction: new_sb_iter

   function vmm_sb_ds_stream_iter#(INP,EXP) new_stream_iter(int exp_stream_id = -1,
                                                             int inp_stream_id = -1);
   
      vmm_sb_ds_stream_iter#(INP,EXP) iter = new(this, null, exp_stream_id, inp_stream_id);
      return iter;
   endfunction: new_stream_iter

   extern function void prepend_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);
   extern function void append_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);
   extern function void unregister_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);

   extern function int get_n_inserted(int exp_stream_id = -1,
                                      int inp_stream_id = -1);
   extern function int get_n_pending(int exp_stream_id = -1,
                                     int inp_stream_id = -1);
   extern function int get_n_matched(int exp_stream_id = -1,
                                     int inp_stream_id = -1);
   extern function int get_n_mismatched(int exp_stream_id = -1,
                                        int inp_stream_id = -1);
   extern function int get_n_dropped(int exp_stream_id = -1,
                                     int inp_stream_id = -1);
   extern function int get_n_not_found(int exp_stream_id = -1,
                                       int inp_stream_id = -1);
   extern function int get_n_orphaned(int exp_stream_id = -1,
                                      int inp_stream_id = -1);

   extern virtual function void report(int exp_stream_id = -1,
                                       int inp_stream_id = -1);
   extern virtual function void describe();
   extern virtual function void display(string prefix = "");

endclass

class vmm_sb_ds  extends vmm_sb_ds_typed #(vmm_data);
   function new(string name, string inst="", vmm_object parent=null);
      super.new(name, inst, parent);
   endfunction

   //`vmm_class_factory(vmm_sb_ds);
endclass


//
// Callback facade class
//
class vmm_sb_ds_callbacks#(type INP=vmm_data, EXP=INP);

   local vmm_sb_ds_typed#(INP,EXP) _temp_typed_sb;
   local vmm_sb_ds                 _temp_sb;
   local vmm_data _temp_data_q[];
   local vmm_data _temp_data;

   virtual function void pre_insert(input vmm_sb_ds sb,
                                    input vmm_data          pkt,
                                    input vmm_sb_ds:: kind_e kind,
                                    ref   int               exp_stream_id,
                                    ref   int               inp_stream_id,
                                    ref   bit               drop);
   endfunction: pre_insert

   virtual function void post_insert(vmm_sb_ds sb,
                                     vmm_data  pkt,
                                     int       exp_stream_id,
                                     int       inp_stream_id);
   endfunction: post_insert

   virtual function void matched(input vmm_sb_ds sb,
                                 input vmm_data  pkt,
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
   endfunction: matched

   virtual function void mismatched(input vmm_sb_ds sb,
                                    input vmm_data  pkt,
                                    input int       exp_stream_id,
                                    input int       inp_stream_id,
                                    ref   int       count);
   endfunction: mismatched

   virtual function void dropped(input vmm_sb_ds sb,
                                 input vmm_data  pkts[],
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
   endfunction: dropped

   virtual function void not_found(input vmm_sb_ds sb,
                                   input vmm_data  pkt,
                                   input int       exp_stream_id,
                                   input int       inp_stream_id,
                                   ref   int       count);
   endfunction: not_found

   virtual function void orphaned(input vmm_sb_ds sb,
                                  input vmm_data  pkts[],
                                  input int       exp_stream_id,
                                  input int       inp_stream_id,
                                  ref   int       count);
   endfunction: orphaned

   virtual function void pre_insert_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                    input EXP          pkt,
                                    input vmm_sb_ds:: kind_e kind,
                                    ref   int               exp_stream_id,
                                    ref   int               inp_stream_id,
                                    ref   bit               drop);
   endfunction: pre_insert_typed

   virtual function void post_insert_typed(vmm_sb_ds_typed#(INP,EXP) sb,
                                     EXP  pkt,
                                     int       exp_stream_id,
                                     int       inp_stream_id);
   endfunction: post_insert_typed

   virtual function void matched_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                 input EXP  pkt,
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
   endfunction: matched_typed

   virtual function void mismatched_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                    input EXP  pkt,
                                    input int       exp_stream_id,
                                    input int       inp_stream_id,
                                    ref   int       count);
   endfunction: mismatched_typed

   virtual function void dropped_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                 input EXP  pkts[],
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
   endfunction: dropped_typed

   virtual function void not_found_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                   input EXP  pkt,
                                   input int       exp_stream_id,
                                   input int       inp_stream_id,
                                   ref   int       count);
   endfunction: not_found_typed

   virtual function void orphaned_typed(input vmm_sb_ds_typed#(INP,EXP) sb,
                                  input EXP  pkts[],
                                  input int       exp_stream_id,
                                  input int       inp_stream_id,
                                  ref   int       count);
   endfunction: orphaned_typed

   /*local*/ function void pre_insert_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                    input EXP          pkt,
                                    input vmm_sb_ds:: kind_e kind,
                                    ref   int               exp_stream_id,
                                    ref   int               inp_stream_id,
                                    ref   bit               drop);
      if($cast(_temp_sb,sb)) begin
		  $cast(_temp_data,pkt);
		  pre_insert(_temp_sb,_temp_data,kind,exp_stream_id,inp_stream_id,drop);
      end
      else if($cast(_temp_typed_sb,sb))
		  pre_insert_typed(_temp_typed_sb,pkt,kind,exp_stream_id,inp_stream_id,drop);
   endfunction: pre_insert_internal

   /*local*/ function void post_insert_internal(vmm_sb_ds_typed#(INP,EXP) sb,
                                     EXP  pkt,
                                     int       exp_stream_id,
                                     int       inp_stream_id);
      if($cast(_temp_sb,sb)) begin
		  $cast(_temp_data , pkt);
		  post_insert(_temp_sb,_temp_data,exp_stream_id,inp_stream_id);
      end
      else if($cast(_temp_typed_sb,sb))
		  post_insert_typed(_temp_typed_sb,pkt,exp_stream_id,inp_stream_id);
   endfunction: post_insert_internal

   /*local*/ function void matched_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                 input EXP  pkt,
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
      if($cast(_temp_sb,sb)) begin
		  $cast(_temp_data, pkt);
		  matched(_temp_sb,_temp_data,exp_stream_id,inp_stream_id,count);
      end
      else if($cast(_temp_typed_sb,sb))
		  matched_typed(_temp_typed_sb,pkt,exp_stream_id,inp_stream_id,count);
   endfunction: matched_internal

   /*local*/ function void mismatched_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                    input EXP  pkt,
                                    input int       exp_stream_id,
                                    input int       inp_stream_id,
                                    ref   int       count);
      if($cast(_temp_sb,sb)) begin
		  $cast(_temp_data, pkt);
		  mismatched(_temp_sb,_temp_data,exp_stream_id,inp_stream_id,count);
      end
      else if($cast(_temp_typed_sb,sb))
		  mismatched_typed(_temp_typed_sb,pkt,exp_stream_id,inp_stream_id,count);
   endfunction: mismatched_internal

   /*local*/ function void dropped_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                 input EXP  pkts[],
                                 input int       exp_stream_id,
                                 input int       inp_stream_id,
                                 ref   int       count);
      if($cast(_temp_sb,sb)) begin
         _temp_data_q = new[pkts.size()];
         for(int i = 0 ; i < pkts.size(); i++)
            $cast(_temp_data_q[i], pkts[i]);
         dropped(_temp_sb,_temp_data_q,exp_stream_id,inp_stream_id,count);
      end
      else if($cast(_temp_typed_sb,sb))
         dropped_typed(_temp_typed_sb,pkts,exp_stream_id,inp_stream_id,count);
   endfunction: dropped_internal

   /*local*/ function void not_found_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                   input EXP  pkt,
                                   input int       exp_stream_id,
                                   input int       inp_stream_id,
                                   ref   int       count);
      if($cast(_temp_sb,sb)) begin
		  $cast(_temp_data, pkt);
		  not_found(_temp_sb,_temp_data,exp_stream_id,inp_stream_id,count);
      end
      else if($cast(_temp_typed_sb,sb))
		  not_found_typed(_temp_typed_sb,pkt,exp_stream_id,inp_stream_id,count);
   endfunction: not_found_internal

   /*local*/ function void orphaned_internal(input vmm_sb_ds_typed#(INP,EXP) sb,
                                  input EXP  pkts[],
                                  input int       exp_stream_id,
                                  input int       inp_stream_id,
                                  ref   int       count);
      if($cast(_temp_sb,sb)) begin
         _temp_data_q = new[pkts.size()];
         for(int i = 0 ; i < pkts.size(); i++)
            $cast(_temp_data_q[i], pkts[i]);
         orphaned(_temp_sb,_temp_data_q,exp_stream_id,inp_stream_id,count);
      end
      else if($cast(_temp_typed_sb,sb))
         orphaned_typed(_temp_typed_sb,pkts,exp_stream_id,inp_stream_id,count);
   endfunction: orphaned_internal
endclass


//
// Status descriptor for notifications
//
class vmm_sb_ds_pkts#(type DATA= vmm_data) extends vmm_data; //TODO CHECK EXTENDS
   DATA          pkts[];
   vmm_sb_ds::kind_e kind;
   int               inp_stream_id;
   int               exp_stream_id;

   /*local*/ function new(DATA          pkt,
                          vmm_sb_ds::kind_e kind,
                          int               exp_stream_id,
                          int               inp_stream_id);
      //super.new(null);

      if (pkt != null) begin
         this.pkts = new [1];
         this.pkts[0] = pkt;
      end
      this.kind = kind;
      this.inp_stream_id = inp_stream_id;
      this.exp_stream_id = exp_stream_id;
   endfunction
endclass


//
// Scoreboard iterator
//
class vmm_sb_ds_iter #(type INP=vmm_data , type EXP=INP);

   local vmm_sb_ds_typed#(INP,EXP) sb;
   local int       exp_str_id;
   local int       inp_str_id;

   local int                   exp_str_idx;
   local vmm_sb_ds_exp_streams#(EXP) exp_str;
   local int                   pkt_str_idx;
   local vmm_sb_ds_pkt_stream#(EXP)  pkt_str;

   local bit is_valid;

   vmm_sb_ds_stream_iter#(INP,EXP) stream_iter;

   /*local*/ extern function new(vmm_sb_ds_typed#(INP,EXP) sb,
                                 int       exp_stream_id,
                                 int       inp_stream_id);
   
   extern function bit first();
   extern function bit is_ok();
   extern function bit next();
   extern function bit last();
   extern function bit prev();
   extern function int length();
   extern function int pos();

   extern function int inp_stream_id();
   extern function int exp_stream_id();
   extern function string describe();

   extern function int get_n_inserted();
   extern function int get_n_pending();
   extern function int get_n_matched();
   extern function int get_n_mismatched();
   extern function int get_n_dropped();
   extern function int get_n_not_found();
   extern function int get_n_orphaned();

   extern function int incr_n_inserted(int delta);
   extern function int incr_n_pending(int delta);
   extern function int incr_n_matched(int delta);
   extern function int incr_n_mismatched(int delta);
   extern function int incr_n_dropped(int delta);
   extern function int incr_n_not_found(int delta);
   extern function int incr_n_orphaned(int delta);

   function vmm_sb_ds_iter#(INP,EXP) copy();
   vmm_sb_ds_iter#(INP,EXP) iter = new(this.sb, this.exp_str_id, this.inp_str_id);
 
   iter.exp_str_idx = this.exp_str_idx;
   iter.exp_str     = this.exp_str;
   iter.pkt_str_idx = this.pkt_str_idx;
   iter.pkt_str     = this.pkt_str;
   iter.is_valid    = this.is_valid;
   iter.stream_iter = this.stream_iter.copy();

   return iter;
endfunction: copy

   function vmm_sb_ds_stream_iter#(INP,EXP) new_stream_iter();
      if (!this.is_valid) begin
         `vmm_error(this.sb.log, "Cannot create stream iterator from invalid scoreboard iterator");
         return null;
      end
   
      return this.sb.new_stream_iter(this.exp_str_idx, this.pkt_str_idx);
   endfunction: new_stream_iter


   extern function int delete();

   extern function void display(string prefix = "");

   function vmm_sb_ds_pkt_stream#(EXP)Xget_pkt_streamX();
      return this.pkt_str;
   endfunction: Xget_pkt_streamX

   extern local function bit next_exp_str();
   extern local function bit next_pkt_str();
   extern local function bit prev_exp_str();
   extern local function bit prev_pkt_str();
endclass: vmm_sb_ds_iter


function vmm_sb_ds_typed::new(string name, string inst="", vmm_object parent=null);
   super.new(name, inst, parent);
   this.log    = new("Data Stream Scoreboard", name);
   this.notify = new(this.log);

   void'(this.notify.configure(INSERTED,   vmm_notify::ONE_SHOT));
   void'(this.notify.configure(EMPTY,      vmm_notify::ON_OFF));
   void'(this.notify.configure(MATCHED,    vmm_notify::ONE_SHOT));
   void'(this.notify.configure(MISMATCHED, vmm_notify::ONE_SHOT));
   void'(this.notify.configure(DROPPED,    vmm_notify::ONE_SHOT));
   void'(this.notify.configure(NOT_FOUND,  vmm_notify::ONE_SHOT));
   void'(this.notify.configure(ORPHANED,   vmm_notify::ONE_SHOT));

   this.notify.indicate(EMPTY);

   begin
      vmm_opts opts = new;
      if (opts.get_bit("sb_trace", "VMM Scoreboard trace ON")) begin
         this.log.set_verbosity(vmm_log::TRACE_SEV);
      end
      if (opts.get_bit("sb_debug", "VMM Scoreboard debug ON")) begin
         this.log.set_verbosity(vmm_log::DEBUG_SEV);
      end
   end
endfunction: new


function int vmm_sb_ds_typed::stream_id(vmm_data          pkt,
                                  vmm_sb_ds_typed::kind_e kind = EITHER);
   return 0;
endfunction: stream_id

function int vmm_sb_ds_typed::inp_stream_id(INP          pkt);
   EXP exp_pkt[] ;
   inp_stream_id = 0;
   void'(this.transform(pkt,exp_pkt)); 
   if(exp_pkt.size > 0 ) 
        inp_stream_id = this.exp_stream_id(exp_pkt[0]);
   else
        return 0;
   return inp_stream_id;
endfunction: inp_stream_id

function int vmm_sb_ds_typed::exp_stream_id(EXP          pkt);
   vmm_data temp;
   if($cast(temp,pkt))
      exp_stream_id = this.stream_id(temp,EXPECT);
   else
      return 0;
endfunction: exp_stream_id

function void vmm_sb_ds_typed::define_stream(int               stream_id,
                                       string            descr = "",
                                       vmm_sb_ds_typed::kind_e kind = EITHER);
   if (stream_id < 0) begin
      `vmm_error(this.log, "vmm_sb_ds::define_stream() called with negative stream_id");
      return;
   end

   case (kind)
     EITHER: begin
        if (this.Xdefine_stream_calledX && !this.Xparallel_streamsX) begin
           `vmm_error(this.log, "vmm_sb_ds::define_stream(): Attempting to define a mix of EITHER and INPUT/EXPECT streams");
        end
        else begin
           this.Xinp_stream_descsX[stream_id] = descr;
           this.Xexp_stream_descsX[stream_id] = descr;
           this.Xparallel_streamsX = 1;

           if (!this.Xexp_streamsX.exists(stream_id)) begin
              vmm_sb_ds_exp_streams#(EXP) exp_streams = new();
              vmm_sb_ds_pkt_stream#(EXP) pkt_stream = new();
              this.Xexp_streamsX[stream_id] = exp_streams;
              this.Xexp_streamsX[stream_id].pkt_streams[stream_id] = pkt_stream;
           end
        end
     end

     INPUT: begin
        if (this.Xdefine_stream_calledX && this.Xparallel_streamsX) begin
           `vmm_error(this.log, "vmm_sb_ds::define_stream(): Attempting to define a mix of EITHER and INPUT/EXPECT streams");
        end
        else begin
           int idx;
           this.Xinp_stream_descsX[stream_id] = descr;

           if (this.Xexp_streamsX.first(idx)) begin
              do
                 if (!this.Xexp_streamsX[idx].pkt_streams.exists(stream_id)) begin
                    vmm_sb_ds_pkt_stream#(EXP) pkt_stream = new();
                    this.Xexp_streamsX[idx].pkt_streams[stream_id] = pkt_stream;
                 end
              while (this.Xexp_streamsX.next(idx));
           end
        end
     end

     EXPECT: begin
        if (this.Xdefine_stream_calledX && this.Xparallel_streamsX) begin
           `vmm_error(this.log, "vmm_sb_ds::define_stream(): Attempting to define a mix of EITHER and INPUT/EXPECT streams");
        end
        else begin
           this.Xexp_stream_descsX[stream_id] = descr;

           if (!this.Xexp_streamsX.exists(stream_id)) begin
              int ip_idx;
              vmm_sb_ds_exp_streams#(EXP) exp_streams = new();
              this.Xexp_streamsX[stream_id] = exp_streams;

              void'(this.Xinp_stream_descsX.first(ip_idx));
              do
                 begin
                    vmm_sb_ds_pkt_stream#(EXP) pkt_stream = new();
                    this.Xexp_streamsX[stream_id].pkt_streams[ip_idx] = pkt_stream;
                 end
              while (this.Xinp_stream_descsX.next(ip_idx));
           end
        end
     end
   endcase
   
   this.Xdefine_stream_calledX = 1;
   
endfunction: define_stream

function bit vmm_sb_ds_typed::inp_insert(INP          pkt,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);
   EXP exp_pkt[] ;
   inp_insert = 0;
   void'(this.transform(pkt,exp_pkt)) ;
   if(inp_stream_id < 0 ) begin
      inp_stream_id = this.inp_stream_id(pkt); 
   end
   if(exp_pkt.size > 0) begin
      for(int i= 0 ; i < exp_pkt.size; i++)
         inp_insert |= this.exp_insert(exp_pkt[i], exp_stream_id, inp_stream_id);
   end
   else
     `vmm_error(this.log,"Cannot transform INPUT pkt to EXPECTED pkt");
   return inp_insert;
endfunction: inp_insert

function bit vmm_sb_ds_typed::exp_insert(EXP          pkt,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);
   vmm_sb_ds_exp_streams#(EXP) exp_streams;
   vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
   bit drop;

   if(pkt == null)
   begin
      `vmm_error(this.log, "Trying to insert null packet to vmm_sb_ds::insert()");
      return 0;
   end

   drop = 0;
   `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                 pre_insert_internal(this, pkt, EXPECT,
                            exp_stream_id, inp_stream_id, drop));
   if (drop) return 1;

   if (inp_stream_id < 0) begin
      inp_stream_id = this.exp_stream_id(pkt); //TODO check exp_stream_id??
   end
   if (this.Xdefine_stream_calledX) begin
      if (!Xinp_stream_descsX.exists(inp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::insert() called with undefined input stream #%0d",
                                        inp_stream_id));
         return 0;
      end
   end

   // Must be an EXPECT packet
   if (exp_stream_id < 0) begin
      exp_stream_id = this.exp_stream_id(pkt);
   end
   
   if (this.Xdefine_stream_calledX) begin
      if (!Xexp_stream_descsX.exists(exp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::insert() called with undefined expected stream #%0d",
                                        exp_stream_id));
         return 0;
      end
   end
   
   `vmm_debug(this.log, $psprintf("Inserting EXPECT packet in stream #%0d->#%0d",
                                  inp_stream_id, exp_stream_id));
   `vmm_verbose(this.log, pkt.psdisplay("   "));

   if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
      exp_streams = new();
      this.Xexp_streamsX[exp_stream_id] = exp_streams;
   end
   else 
      exp_streams = this.Xexp_streamsX[exp_stream_id];

   if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
      pkt_stream = new();
      exp_streams.pkt_streams[inp_stream_id] =  pkt_stream;
   end
   else 
      pkt_stream = exp_streams.pkt_streams[inp_stream_id];

   pkt_stream.pkts.push_back(pkt);
   this.notify.reset(EMPTY);

   pkt_stream.n_inserted++;
   if (!this.insert_recursed) begin
      vmm_sb_ds_pkts#(EXP) status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      this.notify.indicate(INSERTED, status);
   end
   `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                 post_insert_internal(this, pkt, exp_stream_id, inp_stream_id));

   return 1;
endfunction: exp_insert

function bit vmm_sb_ds_typed::insert(vmm_data          pkt,
                               vmm_sb_ds_typed::kind_e kind = INPUT,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);
   vmm_sb_ds_exp_streams#(EXP) exp_streams;
   vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
   bit drop;
   EXP tmp_pkt;
   int fill_thresh;
   bit do_object_thresh_check;
   do_object_thresh_check = vmm_opts::get_bit("object_thresh_check", "Gloabal setting for checking object threshhold in object hierarchy, channel and scoreboard");


   if(pkt == null)
   begin
      `vmm_error(this.log, "Trying to insert null packet to vmm_sb_ds::insert()");
      return 0;
   end

   if (kind == EITHER) begin
      `vmm_error(this.log, "vmm_sb_ds::insert() called with EITHER packet kind");
      return 0;
   end

   if(!$cast(tmp_pkt,pkt)) begin
      `vmm_error(this.log,"Incompatible type passed to vmm_sb_ds::insert method. For non vmm_data extensions use inp_insert or exp_insert");
       return 0;
   end
   drop = 0;
   `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                 pre_insert_internal(this, tmp_pkt, kind,
                            exp_stream_id, inp_stream_id, drop));
   if (drop) return 1;

   if (inp_stream_id < 0) begin
      inp_stream_id = this.stream_id(pkt, INPUT);
   end
   if (this.Xdefine_stream_calledX) begin
      if (!Xinp_stream_descsX.exists(inp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::insert() called with undefined input stream #%0d",
                                        inp_stream_id));
         return 0;
      end
   end

   if (kind == INPUT) begin
      EXP out_pkts[];
      INP inp_pkt;
      vmm_data tmp_data;
      if(!$cast(inp_pkt,pkt)) begin
         `vmm_error(this.log,"Incompatible INPUT type passed to vmm_sb_ds::insert.Use inp_insert insert");
          return 0;
      end
      `vmm_debug(this.log, $psprintf("Inserting INPUT packet in stream #%0d",
                                     inp_stream_id));
      `vmm_verbose(this.log, pkt.psdisplay("   "));

      void'(this.transform(inp_pkt, out_pkts));
      this.insert_recursed = 1;
      foreach (out_pkts[i])  begin
         if(!$cast(tmp_data,out_pkts[i])) begin
            `vmm_error(this.log,"Non vmm_data derivative used in vmm_sb_ds::insert. Use exp_insert or inp_insert");
            return 0;
         end
         void'(this.insert(tmp_data, EXPECT, exp_stream_id, inp_stream_id));
      end
      this.insert_recursed = 0;

      begin
         vmm_sb_ds_pkts#(EXP) status = new(null, EXPECT, exp_stream_id, inp_stream_id);
         status.pkts = new [out_pkts.size()] (out_pkts);
         this.notify.indicate(INSERTED, status);
      end

      return 1;
   end

   // Must be an EXPECT packet
   if (exp_stream_id < 0) begin
      exp_stream_id = this.stream_id(pkt, EXPECT);
   end
   
   if (this.Xdefine_stream_calledX) begin
      if (!Xexp_stream_descsX.exists(exp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::insert() called with undefined expected stream #%0d",
                                        exp_stream_id));
         return 0;
      end
   end
   
   `vmm_debug(this.log, $psprintf("Inserting EXPECT packet in stream #%0d->#%0d",
                                  inp_stream_id, exp_stream_id));
   `vmm_verbose(this.log, pkt.psdisplay("   "));

   if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
      exp_streams = new();
      this.Xexp_streamsX[exp_stream_id] = exp_streams;
   end
   else 
      exp_streams = this.Xexp_streamsX[exp_stream_id];

   if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
      pkt_stream = new();
      exp_streams.pkt_streams[inp_stream_id] =  pkt_stream;
   end
   else 
      pkt_stream = exp_streams.pkt_streams[inp_stream_id];

   if(!$cast(tmp_pkt,pkt))
      return 0;
   pkt_stream.pkts.push_back(tmp_pkt);
   this.notify.reset(EMPTY);
   
   //check fill threshhold
   fill_thresh = vmm_opts::get_int("sb_ds_fill_thresh", 1000, "GLOBAL option that sets the number of objects threshold in a datastream scoreboard");
   if (do_object_thresh_check && pkt_stream.pkts.size() >= fill_thresh) 
      `vmm_warning(this.log, `vmm_sformatf("The number of objects in the scoreboard[%s] passes the specified threshold ( = %0d ) indicating a potential garbage collection/memory leak problem. Please be aware that there might be problem with response observer(s) or increase the threshold.", this.log.get_instance(), fill_thresh));


   pkt_stream.n_inserted++;
   if (!this.insert_recursed) begin
      vmm_sb_ds_pkts#(EXP) status = new(tmp_pkt, EXPECT, exp_stream_id, inp_stream_id);
      this.notify.indicate(INSERTED, status);
   end
   `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                 post_insert_internal(this, tmp_pkt, exp_stream_id, inp_stream_id));

   return 1;
endfunction: insert

function bit vmm_sb_ds_typed::remove(vmm_data          pkt,
                               vmm_sb_ds::kind_e kind = INPUT,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);

   vmm_sb_ds_exp_streams#(EXP) exp_streams;
   vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
   EXP tmp_pkt;
   if (kind == EITHER) begin
      `vmm_error(this.log, "vmm_sb_ds::remove() called with EITHER packet kind");
      return 0;
   end
   if(!$cast(tmp_pkt,pkt)) begin
      `vmm_error(this.log,"vmm_sb_ds::remove. Incompatiable data type used. Used exp_remove or inp_remove");
   end

   if (inp_stream_id < 0) begin
      inp_stream_id = this.stream_id(pkt, INPUT);
   end
   if (this.Xdefine_stream_calledX) begin
      if (!Xinp_stream_descsX.exists(inp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::remove() called with undefined input stream #%0d",
                                        inp_stream_id));
         return 0;
      end
   end

   if (kind == INPUT) begin
      EXP out_pkts[];
      INP inp_temp;
      bit      rc = 1;
      
      `vmm_trace(this.log, $psprintf("Deleting INPUT packet from stream #%0d",
                                     inp_stream_id));
      `vmm_verbose(this.log, pkt.psdisplay("   "));

      if(!$cast(inp_temp,pkt)) begin
         `vmm_error(this.log,"vmm_sb_ds::remove. Incompatiable data type used. Use inp_remove or exp_remove");
         return 0;
      end
      void'(this.transform(inp_temp, out_pkts));
      foreach (out_pkts[i])  begin
        vmm_data data_temp;
        if(!$cast(data_temp,out_pkts[i])) begin
           `vmm_error(this.log,"vmm_sb_ds::remove.Incompatiable data type used. Use exp_remove or inp_remove");
           return 0;
        end
         rc |= this.remove(data_temp, EXPECT, exp_stream_id, inp_stream_id);
      end

      return rc;
   end

   // Must be an EXPECT packet
   if (exp_stream_id < 0) begin
      exp_stream_id = this.stream_id(pkt, EXPECT);
   end
   
   if (this.Xdefine_stream_calledX) begin
      if (!Xexp_stream_descsX.exists(exp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::remove() called with undefined expected stream #%0d",
                                        exp_stream_id));
         return 0;
      end
   end
   
   `vmm_trace(this.log, $psprintf("Deleting EXPECT packet from stream #%0d->#%0d",
                                  inp_stream_id, exp_stream_id));
   `vmm_verbose(this.log, pkt.psdisplay("   "));

   if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
      `vmm_error(this.log, $psprintf("vmm_sb_ds::remove(): Cannot find packet to remove: expected stream #%0d does not exist",
                                     exp_stream_id));
      return 0;
   end
   exp_streams = this.Xexp_streamsX[exp_stream_id];

   if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
      `vmm_error(this.log, $psprintf("vmm_sb_ds::remove(): Cannot find packet to remove: stream #%0d->#%0d does not exist.",
                                     inp_stream_id, exp_stream_id));
      return 0;
   end
   pkt_stream = exp_streams.pkt_streams[inp_stream_id];

   foreach (pkt_stream.pkts[i]) begin
      if (this.compare(tmp_pkt, pkt_stream.pkts[i])) begin
         pkt_stream.pkts.delete(i);
         if (pkt_stream.pkts.size() == 0) begin
            // The entire scoreboard might be empty!
            if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
         end
         return 1;
      end
   end

   `vmm_error(this.log, "vmm_sb_ds::remove(): Cannot find packet to remove");

   return 0;
endfunction: remove

function bit vmm_sb_ds_typed::inp_remove(INP           pkt,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);
   EXP exp_pkt[] ;
   inp_remove = 0;
   if(inp_stream_id < 0 ) 
      inp_stream_id = this.inp_stream_id(pkt);
   void'(this.transform(pkt,exp_pkt));
   if(exp_pkt.size > 0 ) begin
      foreach(exp_pkt[i])
         inp_remove = this.exp_remove(exp_pkt[i],  exp_stream_id, inp_stream_id);
   end
   else
     `vmm_error(this.log,"vmm_sb_ds::inp_remove:Cannot transform INPUT pkt to EXPECTED pkt");
   return inp_remove;

endfunction: inp_remove

function bit vmm_sb_ds_typed::exp_remove(EXP          pkt,
                               int               exp_stream_id = -1,
                               int               inp_stream_id = -1);

   vmm_sb_ds_exp_streams#(EXP) exp_streams;
   vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;

   if (inp_stream_id < 0) begin
      inp_stream_id = this.exp_stream_id(pkt); 
   end
   if (this.Xdefine_stream_calledX) begin
      if (!Xinp_stream_descsX.exists(inp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::remove() called with undefined input stream #%0d",
                                        inp_stream_id));
         return 0;
      end
   end

   // Must be an EXPECT packet
   if (exp_stream_id < 0) begin
      exp_stream_id = this.exp_stream_id(pkt);
   end
   
   if (this.Xdefine_stream_calledX) begin
      if (!Xexp_stream_descsX.exists(exp_stream_id)) begin
         `vmm_error(this.log, $psprintf("vmm_sb_ds::remove() called with undefined expected stream #%0d",
                                        exp_stream_id));
         return 0;
      end
   end
   
   `vmm_trace(this.log, $psprintf("Deleting EXPECT packet from stream #%0d->#%0d",
                                  inp_stream_id, exp_stream_id));
   `vmm_verbose(this.log, pkt.psdisplay("   "));

   if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
      `vmm_error(this.log, $psprintf("vmm_sb_ds::remove(): Cannot find packet to remove: expected stream #%0d does not exist",
                                     exp_stream_id));
      return 0;
   end
   exp_streams = this.Xexp_streamsX[exp_stream_id];

   if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
      `vmm_error(this.log, $psprintf("vmm_sb_ds::remove(): Cannot find packet to remove: stream #%0d->#%0d does not exist.",
                                     inp_stream_id, exp_stream_id));
      return 0;
   end
   pkt_stream = exp_streams.pkt_streams[inp_stream_id];

   foreach (pkt_stream.pkts[i]) begin
      if (this.compare(pkt, pkt_stream.pkts[i])) begin
         pkt_stream.pkts.delete(i);
         if (pkt_stream.pkts.size() == 0) begin
            // The entire scoreboard might be empty!
            if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
         end
         return 1;
      end
   end

   `vmm_error(this.log, "vmm_sb_ds::remove(): Cannot find packet to remove");

   return 0;
endfunction: exp_remove

function bit vmm_sb_ds_typed::transform(input  INP in_pkt,
                                  output EXP out_pkts[]);
   EXP temp;
   if($cast(temp,in_pkt)) begin
      out_pkts = new[1];
      out_pkts[0] = temp;
   end
   else begin
      `vmm_error(this.log,"Cannot perfrom transform operation. Please provide an implementation of transform method in vmm_sb_ds extension");
      return 0;
   end
endfunction: transform


function bit vmm_sb_ds_typed::match(EXP actual,
                              EXP expected);
   return this.quick_compare(actual, expected);
endfunction: match

function bit vmm_sb_ds_typed::quick_compare(EXP actual,
                                      EXP expected);
   return 1;
endfunction: quick_compare

function bit vmm_sb_ds_typed::compare(EXP actual,
                                EXP expected);

   string diff;
   if (this.quick_compare(actual, expected)) begin
         return actual.compare(expected, diff);
   end

endfunction: compare

function bit vmm_sb_ds_typed::expect_with_losses(input  EXP pkt,
                                           output EXP matched,
                                           output EXP lost[],
                                           input  int      exp_stream_id = -1,
                                           input  int      inp_stream_id = -1,
                                           input  bit      silent = 0);

   vmm_sb_ds_exp_streams#(EXP) exp_streams;
   vmm_sb_ds_pkt_stream#(EXP)  pkt_stream;
   int                   match_idx;

   if(pkt == null)
   begin
     `vmm_error(this.log,"Null vmm_data pointer provided to vmm_sb_ds::expect_with_losses");
     return 0;
   end

   matched = null;
   lost = new [0];

   if (inp_stream_id < 0) begin
      vmm_data tmp_data;
      if($cast(tmp_data,pkt))
         inp_stream_id = this.stream_id(tmp_data,INPUT);
      else
         inp_stream_id = this.exp_stream_id(pkt); 
   end
   if (exp_stream_id < 0) begin
      vmm_data tmp_data;
      if($cast(tmp_data,pkt))
         exp_stream_id = this.stream_id(tmp_data,EXPECT);
      else
         exp_stream_id = this.exp_stream_id(pkt);
   end

   `vmm_debug(this.log, $psprintf("Looking for packet on stream #%0d->#%0d",
                                  inp_stream_id, exp_stream_id));
   `vmm_verbose(this.log, pkt.psdisplay("   "));

   if (!this.Xexp_streamsX.exists(exp_stream_id)) begin
      // Not found because the output stream does not exist!
      vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      int n = 1;

      this.notify.indicate(NOT_FOUND, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

      if (!silent) begin
         this.n_not_found += n;
         `vmm_error(this.log, $psprintf("With-loss packet was not found: EXPECT stream #%0d does not exist.", exp_stream_id));
      end
      return 0;
   end
   exp_streams = this.Xexp_streamsX[exp_stream_id];

   if (!exp_streams.pkt_streams.exists(inp_stream_id)) begin
      // Not found because the input stream does not exist!
      vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      int n = 1;

      this.notify.indicate(NOT_FOUND, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

      if (!silent) begin
         this.n_not_found += n;
         `vmm_error(this.log, $psprintf("With-loss packet was not found: Stream #%0d->%0d does not exist.", inp_stream_id, exp_stream_id));
      end
      return 0;
   end
   pkt_stream = exp_streams.pkt_streams[inp_stream_id];

   if (pkt_stream.pkts.size() == 0) begin
      // Not found because the packet stream is empty!
      vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      int n = 1;

      this.notify.indicate(NOT_FOUND, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

      if (!silent) begin
         pkt_stream.n_not_found += n;
         `vmm_error(this.log, $psprintf("With-loss packet was not found: Stream #%0d->%0d is empty.", inp_stream_id, exp_stream_id));
      end
      return 0;
   end      

`ifdef VCS
   foreach (pkt_stream.pkts[i]) begin
   `else
   for(int i=0; i<pkt_stream.pkts.size(); i++) begin
   `endif   
      if (this.match(pkt, pkt_stream.pkts[i])) begin
         // We have a match!
         matched = pkt_stream.pkts[i];
         match_idx = i;
         break;
      end
   end
   if (matched == null) begin
      // Not found because no packet matched
      vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      int n = 1;

      this.notify.indicate(NOT_FOUND, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       not_found_internal(this, pkt, exp_stream_id, inp_stream_id, n));

      if (!silent) begin
         this.n_not_found += n;
         `vmm_error(this.log, {"With-loss packet was not matched:\n",
                               pkt.psdisplay("   ")});
      end
      return 0;
   end


   // Everything between the matching packet and the head
   // of the packet stream is assumed to have been lost
   if (match_idx > 0) begin
      lost = new [match_idx];
      foreach (lost[i]) begin
         lost[i] = pkt_stream.pkts[i];
      end

      begin
         vmm_sb_ds_pkts#(EXP)status = new(null, EXPECT, exp_stream_id, inp_stream_id);
         int n = lost.size();

         status.pkts = new [lost.size()] (lost);
         this.notify.indicate(DROPPED, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          dropped_internal(this, status.pkts, exp_stream_id, inp_stream_id, n));
         if (!silent) pkt_stream.n_dropped += n;
      end
   end
   repeat (match_idx + 1) void'(pkt_stream.pkts.pop_front());
   if (pkt_stream.pkts.size() == 0) begin
      // The entire scoreboard might be empty!
      if (this.get_n_pending() == 0) this.notify.indicate(EMPTY);
   end

   if (!this.compare(pkt, matched)) begin
      // Mis-match!

       `vmm_trace(this.log, $psprintf("packet mismatched expected packet in stream #%0d->#%0d\n%s\n%s",
                                  inp_stream_id, exp_stream_id,
                                  pkt.psdisplay("   Actual:"),
                                  matched.psdisplay("   Msmtch:")));

      begin
         vmm_sb_ds_pkts#(EXP)status = new(null, EXPECT, exp_stream_id, inp_stream_id);
         int n = 1;

         status.pkts = new [2];
         status.pkts[0] = pkt;
         status.pkts[1] = matched;

         this.notify.indicate(MISMATCHED, status);
         `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                          mismatched_internal(this, pkt, exp_stream_id, inp_stream_id, n));
         if (!silent) pkt_stream.n_mismatched += n;
      end

      if (!silent) begin
         `vmm_error(this.log, $psprintf("With-loss packet was not found"));
      end
      return 0;
   end

   begin
      vmm_sb_ds_pkts#(EXP)status = new(pkt, EXPECT, exp_stream_id, inp_stream_id);
      int n = 1;

      this.notify.indicate(MATCHED, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       matched_internal(this, pkt, exp_stream_id, inp_stream_id, n));
      if (!silent) pkt_stream.n_matched += n;
   end

   return 1;
endfunction: expect_with_losses

function void vmm_sb_ds_typed::write_inp(int id=-1, INP trans);
   `vmm_error(this.log,"vmm_sb_ds class function write_inp is not extended.");
endfunction
   
function void vmm_sb_ds_typed::write_exp(int id=-1, EXP trans);
   `vmm_error(this.log,"vmm_sb_ds class function write_exp is not extended.");
endfunction

function void vmm_sb_ds_typed::flush();
   this.Xinp_stream_descsX.delete();
   this.Xexp_stream_descsX.delete();
   this.Xexp_streamsX.delete();
   this.Xdefine_stream_calledX = 0;

   this.n_not_found = 0;
   this.insert_recursed = 0;

   this.notify.indicate(EMPTY);
endfunction: flush

function void vmm_sb_ds_typed::prepend_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to prepend a NULL callback extension");
      return;
   end

   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Prepend new callback
   this.callbacks.push_front(cb);
endfunction: prepend_callback


function void vmm_sb_ds_typed::append_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);
   if (cb == null) begin
      `vmm_error(this.log, "Attempting to append a NULL callback extension");
      return;
   end

   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         `vmm_warning(this.log, "Callback has already been registered");
         return;
      end
   end
   //Append new callback
   this.callbacks.push_back(cb);
endfunction: append_callback


function void vmm_sb_ds_typed::unregister_callback(vmm_sb_ds_callbacks#(INP,EXP) cb);
   foreach(this.callbacks[i]) begin
      if (this.callbacks[i] == cb) begin
         // Unregister it
         this.callbacks.delete(i);
         return;
      end
   end

   `vmm_warning(this.log, "Callback was not registered");
endfunction: unregister_callback


function int vmm_sb_ds_typed::get_n_inserted(int exp_stream_id = -1,
                                       int inp_stream_id = -1);
   int n = 0;

   vmm_sb_ds_iter #(INP,EXP)iter;
   iter = new (this, exp_stream_id, inp_stream_id);
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream#(EXP) pkt_str;
      pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.n_inserted;
   end

   return n;
endfunction: get_n_inserted


function int vmm_sb_ds_typed::get_n_pending(int exp_stream_id = -1,
                                      int inp_stream_id = -1);
   int n = 0;

   vmm_sb_ds_iter #(INP,EXP)iter = new (this, exp_stream_id, inp_stream_id);
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream#(EXP) pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.pkts.size();
   end

   return n;
endfunction: get_n_pending


function int vmm_sb_ds_typed::get_n_matched(int exp_stream_id = -1,
                                      int inp_stream_id = -1);
   int n = 0;

   vmm_sb_ds_iter#(INP,EXP) iter = new (this, exp_stream_id, inp_stream_id);
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream #(EXP)pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.n_matched;
   end

   return n;
endfunction: get_n_matched


function int vmm_sb_ds_typed::get_n_mismatched(int exp_stream_id = -1,
                                         int inp_stream_id = -1);
   int n = 0;

   vmm_sb_ds_iter #(INP,EXP)iter = new (this, exp_stream_id, inp_stream_id);
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream#(EXP) pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.n_mismatched;
   end

   return n;
endfunction: get_n_mismatched


function int vmm_sb_ds_typed::get_n_dropped(int exp_stream_id = -1,
                                      int inp_stream_id = -1);
   int n = 0;

   vmm_sb_ds_iter#(INP,EXP) iter = new (this, exp_stream_id, inp_stream_id);
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream #(EXP)pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.n_dropped;
   end

   return n;
endfunction: get_n_dropped


function int vmm_sb_ds_typed::get_n_not_found(int exp_stream_id = -1,
                                        int inp_stream_id = -1);
   int n = 0;


   vmm_sb_ds_iter #(INP,EXP)iter = new (this, exp_stream_id, inp_stream_id);

   while (iter.next()) begin
      vmm_sb_ds_pkt_stream#(EXP) pkt_str = iter.Xget_pkt_streamX();
      n += pkt_str.n_not_found;
   end

   if (exp_stream_id < 0 || inp_stream_id < 0) n += this.n_not_found;

   return n;
endfunction: get_n_not_found


function int vmm_sb_ds_typed::get_n_orphaned(int exp_stream_id = -1,
                                       int inp_stream_id = -1);

   vmm_sb_ds_iter#(INP,EXP) iter = new (this, exp_stream_id, inp_stream_id);
   EXP pkts[$];
   int n = 0 ;
   while (iter.next()) begin
      vmm_sb_ds_pkt_stream#(EXP) pkt_stream = iter.Xget_pkt_streamX();

      // Not yet supported in SP1
      // pkts = '{pkts, pkt_stream.pkts};
      foreach (pkt_stream.pkts[i]) pkts.push_back(pkt_stream.pkts[i]);
   end

   if (pkts.size() > 0) begin
      vmm_sb_ds_pkts#(EXP)status = new(null, EXPECT, -1, -1);
      n = pkts.size();

      status.pkts = new [pkts.size()];
      foreach (pkts[i]) status.pkts[i] = pkts[i];
      this.notify.indicate(ORPHANED, status);
      `vmm_callback(vmm_sb_ds_callbacks#(INP,EXP),
                       orphaned_internal(this, status.pkts,
                                exp_stream_id, inp_stream_id, n));
   end

   return n; 
endfunction: get_n_orphaned


function void vmm_sb_ds_typed::report(int exp_stream_id = -1,
                                int inp_stream_id = -1);
   vmm_sb_ds_iter#(INP,EXP) iter = new (this, exp_stream_id, inp_stream_id);

   string s = this.log.get_instance();
   if (s.len() < 30) s = {s, {(30 - s.len()){" "}}};
   else if (s.len() > 30) s = s.substr(0, 29);
          
   $write("+--------------------------------+------+------+------+------+------+------+\n");
   $write("| %s |%s|%s|%s|%s|%s|%s|\n", s,
          "Insert", "Matchd", "MsMtch", "Droppd", "NotFnd", "Orphan");
   $write("+--------------------------------+------+------+------+------+------+------+\n");

   while (iter.next()) begin
      s = iter.describe();
      if (s.len() < 30) s = {s, {(30 - s.len()){" "}}};
      else if (s.len() > 30) s = s.substr(0, 29);
      $write("| %s | %04d | %04d | %04d | %04d | %04d | %04d |\n", s,
             iter.get_n_inserted(), iter.get_n_matched(),
             iter.get_n_mismatched(), iter.get_n_dropped(),
             iter.get_n_not_found(), iter.get_n_orphaned());
   end
   $write("+--------------------------------+------+------+------+------+------+------+\n");
   $write("|                          TOTAL | %04d | %04d | %04d | %04d | %04d | %04d |\n",
          this.get_n_inserted(exp_stream_id, inp_stream_id),
          this.get_n_matched(exp_stream_id, inp_stream_id),
          this.get_n_mismatched(exp_stream_id, inp_stream_id),
          this.get_n_dropped(exp_stream_id, inp_stream_id),
          this.get_n_not_found(exp_stream_id, inp_stream_id),
          this.get_n_orphaned(exp_stream_id, inp_stream_id));
   $write("+--------------------------------+------+------+------+------+------+------+\n\n");
endfunction: report


function void vmm_sb_ds_typed::describe();
   vmm_sb_ds_iter#(INP,EXP) iter = this.new_sb_iter();

   $write("Streams in Data Stream Scoreboard \"%s\":\n",
          this.log.get_instance());

   while (iter.next()) begin
      $write("   %s\n", iter.describe());
   end
endfunction: describe


function void vmm_sb_ds_typed::display(string prefix = "");
   $write("%sContent of Data Stream Scoreboard \"%s\":\n", prefix, 
          this.log.get_instance());

   if (this.Xparallel_streamsX) begin
      foreach (this.Xexp_streamsX[k]) begin
         vmm_sb_ds_exp_streams#(EXP) exp_str = this.Xexp_streamsX[k];
         vmm_sb_ds_pkt_stream#(EXP)  pkt_str = exp_str.pkt_streams[k];

         if (pkt_str == null) continue;

         $write("%s   Stream #%0d", prefix, k);
         if (this.Xexp_stream_descsX.exists(k)) begin
            $write(" (%s)", this.Xexp_stream_descsX[k]);
         end
         $write(":\n");

         foreach (pkt_str.pkts[i]) begin
            pkt_str.pkts[i].display({prefix, "      "});
         end
      end

      return;
   end

   foreach (this.Xexp_streamsX[k]) begin
      vmm_sb_ds_exp_streams#(EXP) exp_str = this.Xexp_streamsX[k];

      $write("%s   To stream #%0d", prefix, k);
      if (this.Xexp_stream_descsX.exists(k)) begin
         $write(" (%s)", this.Xexp_stream_descsX[k]);
      end
      $write(":\n");
      foreach (exp_str.pkt_streams[j]) begin
         vmm_sb_ds_pkt_stream#(EXP) pkt_str = exp_str.pkt_streams[j];

         $write("%s      From stream #%0d", prefix, j);
         if (this.Xinp_stream_descsX.exists(j)) begin
            $write(" (%s)", this.Xinp_stream_descsX[j]);
         end
         $write(":\n");
         foreach (pkt_str.pkts[i]) begin
            pkt_str.pkts[i].display({prefix, "      "});
         end
      end
   end
endfunction: display


`endif // VMM_SB_DS_SV
