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

class Scoreboard extends vmm_xactor;
  static int DONE;
  static int pkts_checked = 0;
  static int gen_pkt_count = 0;
  static int sent_pkt_count = 0;
  static int recvd_pkt_count = 0;

  protected bit[3:0] sa, da;
  Packet         refPkts[$];
  Packet         genPkts[$];
  Packet         pktsent;

  vmm_tlm_nb_transport_fw_export#(Scoreboard, Packet) socket = new(this,"Scoreboard_export",100,0);

  int coverage_filter_size;
  int coverage_filter_warnings;
  int pkts_from_receiver = 0;
  int warning = 0, coverage_repeated = 0;
  real coverage_result, coverage_result_prev = 0;
  Packet pkt;

  covergroup sb_cov;
    coverpoint sa { option.weight = 0; }
    coverpoint da { option.weight = 0; }
    cross sa, da;
  endgroup

   function new(string instance);
     super.new("Scoreboard", instance);
     `vmm_trace(this.log, $psprintf("%m"));
     this.DONE     = this.notify.configure(-1, vmm_notify::ON_OFF);
     this.coverage_filter_warnings = 100; // terminates simulation if exceeded
     this.sb_cov = new();
   endfunction
   
   function vmm_tlm::sync_e nb_transport_fw(int id =-1, Packet pkt, ref vmm_tlm::phase_e ph, ref int delay);
       `vmm_debug(this.log, pkt.psdisplay("Receiver to Scoreboard"));
       this.recvd_pkt_count++;
       check(pkt);
       this.pkts_checked++;
       this.coverage_result_prev = this.coverage_result;
       this.coverage_result = $get_coverage();
       if (this.coverage_result == 100) begin
         `vmm_note(this.log, $psprintf("%0d packets checked.  Coverage = %0f", this.pkts_checked, this.coverage_result));
         this.notify.indicate(this.DONE);
         return vmm_tlm::TLM_COMPLETED;
       end
       if (this.coverage_result == this.coverage_result_prev) begin
         this.coverage_filter_size = (this.coverage_result * 16 * 16 * 4)/100 + 100;
         if (++this.coverage_repeated >= this.coverage_filter_size) begin
           if (++this.warning >= this.coverage_filter_warnings + 10) begin
             `vmm_warning(this.log, $psprintf("Terminating Point Reached.  %0d packets checked.  Coverage = %0f\n", pkts_checked, this.coverage_result));
             this.notify.indicate(this.DONE);
             return vmm_tlm::TLM_COMPLETED;
           end
           if (this.warning >= this.coverage_filter_warnings) begin
             `vmm_warning(this.log, $psprintf("Diminished Return Reached.  %0d packets checked.  Coverage = %0f\n", pkts_checked, this.coverage_result));
             return vmm_tlm::TLM_COMPLETED;
           end
           `vmm_warning(this.log, $psprintf("Repeating coverage %0d times.  %0d packets checked.  Coverage = %0f\n", warning + this.coverage_filter_size, pkts_checked, this.coverage_result));
           return vmm_tlm::TLM_COMPLETED;
         end
       end
       else begin
         this.coverage_repeated = 0;
         this.warning = 0;
       end
       `vmm_note(this.log, $psprintf("%0d packets checked.  Coverage = %0f", this.pkts_checked, this.coverage_result));
       return vmm_tlm::TLM_ACCEPTED;
   endfunction
   
   function void deposit_sentpkt(Packet pkt);
     string dontcare;
     `vmm_trace(this.log, $psprintf("%m"));
     `vmm_debug(log, pkt.psdisplay("Driver to Scoreboard"));
     refPkts.push_back(pkt);
     sent_pkt_count++;
   endfunction
   
   function void check(Packet pktrecvd);
     int    index[$];
     string diff;
     `vmm_trace(this.log, $psprintf("%m"));
   
     index = refPkts.find_first_index() with (item.da == pktrecvd.da);
     if (index.size() <= 0)
       `vmm_fatal(log, $psprintf("Matching packet not found\n%m\n\n"));
     pktsent = refPkts[index[0]];
     refPkts.delete(index[0]);
   
     this.sa = pktsent.sa;
     this.da = pktsent.da;
     sb_cov.sample();
   endfunction
   
   function int final_check();
     `vmm_trace(this.log, $psprintf("%m"));
     final_check = (genPkts.size() || refPkts.size()) ? 0 : 1;
   endfunction
   
   function void report();
     `vmm_trace(this.log, $psprintf("%m"));
     foreach(refPkts[i])
       `vmm_warning(log, $psprintf("packet#%0d.%0d.%0d was sent into Router but not checked\n", refPkts[i].stream_id, refPkts[i].scenario_id, refPkts[i].data_id));
     $display("[Scoreboard]: %0d packets generated, %0d packets sent, %0d packets sampled, %0d packets checked\n", gen_pkt_count, sent_pkt_count, recvd_pkt_count, pkts_checked);
   endfunction
   
endclass
