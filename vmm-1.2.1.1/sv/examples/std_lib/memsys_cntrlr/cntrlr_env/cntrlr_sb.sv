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





`include "vmm_sb.sv"

class cpu2sram_sb extends vmm_sb_ds_typed#(cpu_trans, sram_trans);

   int addr_wdth = 6;

   function new(string inst, int num_sram_devices, int addr_wdth);
      super.new(inst);
      this.define_stream(0, "CPU", INPUT);
      for (int i=0; i<num_sram_devices;  i++) begin
          string sname = $psprintf("SRAM_%0d", i);
          this.define_stream(i, sname, EXPECT);
      end
      this.addr_wdth = addr_wdth;
   endfunction

   function bit transform(input cpu_trans in_pkt,
                                 output sram_trans out_pkts[]);
      out_pkts = new[1];
      out_pkts[0] = new();
      out_pkts[0].kind    = sram_trans::kind_e'(in_pkt.kind);
      out_pkts[0].address = in_pkt.address;
      out_pkts[0].data    = in_pkt.data;
      //decoding logic has to be added
   endfunction

  virtual function bit compare(sram_trans actual, sram_trans expected);
     if (actual.kind == sram_trans::WRITE) begin
        `vmm_note(log, $psprintf("WRITE @0x%x  data=0x%x", expected.address, expected.data));
        return ((actual.address[5:0] == expected.address[5:0]) && (actual.data == expected.data));
     end
     else begin
        return ((actual.kind == expected.kind) && (actual.address[5:0] == expected.address[5:0]));
     end
  endfunction

   virtual function void write_SRAM(int id=-1, sram_trans tr);
   endfunction

   virtual function void write_CPU(int id=-1, cpu_trans tr);
   endfunction


endclass


class sram2cpu_sb extends vmm_sb_ds_typed#(sram_trans, cpu_trans);
   int addr_wdth = 6;

   function new(string inst, int num_sram_devices, int addr_wdth = 6);
      super.new(inst);
      for (int i=0; i<num_sram_devices;  i++) begin
          string sname = $psprintf("SRAM_%0d", i);
          this.define_stream(i, sname, INPUT);
      end
      this.define_stream(0, "CPU", EXPECT);
      this.addr_wdth = addr_wdth;
   endfunction

   function bit transform(input sram_trans in_pkt,
                         output cpu_trans out_pkts[]);
      out_pkts = new[1];
      out_pkts[0] = new();
      out_pkts[0].kind    = cpu_trans::kind_e'(in_pkt.kind);
      out_pkts[0].address = in_pkt.address;
      out_pkts[0].data    = in_pkt.data;
      //decoding logic has to be added
   endfunction

  virtual function bit compare(cpu_trans actual, cpu_trans expected);
     if (actual.kind == sram_trans::WRITE) begin
        return (1);
     end
     else begin
        `vmm_note(log, $psprintf("READ @0x%x  data=0x%x", actual.address, actual.data));
        return ((actual.kind == expected.kind) && (actual.data == expected.data));
     end
  endfunction

endclass

