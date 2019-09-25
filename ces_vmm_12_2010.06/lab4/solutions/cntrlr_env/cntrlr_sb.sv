`include "vmm_sb.sv"

class cpu2sram_sb extends vmm_sb_ds_typed#(cpu_trans, sram_trans);

   function new(string inst, int num_sram_devices);
      super.new(inst);
	  // Lab 4 - Define streams based on how many logical INPUT and OUTPUT streams there are
      this.define_stream(0, "CPU", INPUT);
      for (int i=0; i<num_sram_devices;  i++) begin
          string sname = $psprintf("SRAM_%0d", i);
          this.define_stream(i, sname, EXPECT);
      end
   endfunction

   virtual function bit transform(input cpu_trans in_pkt,
                                 output sram_trans out_pkts[]);
      // Lab 4 - Apply transformation to transform INP packet to EXP packet
      out_pkts = new[1];
      out_pkts[0] = new();
      out_pkts[0].kind    = sram_trans::kind_e'(in_pkt.kind);
      out_pkts[0].address = in_pkt.address;
      out_pkts[0].data    = in_pkt.data;
      //decoding logic has to be added
   endfunction

  virtual function bit compare(sram_trans actual, sram_trans expected);
     
	 // Lab 4 - Override the scoreboard function to compare the address and data fields.
     if (actual.kind == sram_trans::WRITE) begin
        `vmm_note(log, $psprintf("WRITE @0x%x  data=0x%x", expected.address, expected.data));
        return ((actual.address[5:0] == expected.address[5:0]) && (actual.data == expected.data));
     end
     else begin
        return ((actual.kind == expected.kind) && (actual.address[5:0] == expected.address[5:0]));
     end
  endfunction

endclass


class sram2cpu_sb extends vmm_sb_ds_typed#(sram_trans, cpu_trans);

   function new(string inst, int num_sram_devices);
      super.new(inst);
	  // Lab 4 - Define streams based on how many logical INPUT and OUTPUT streams there are
      for (int i=0; i<num_sram_devices;  i++) begin
          string sname = $psprintf("SRAM_%0d", i);
          this.define_stream(i, sname, INPUT);
      end
      this.define_stream(0, "CPU", EXPECT);
   endfunction

   virtual function bit transform(input sram_trans in_pkt,
                         output cpu_trans out_pkts[]);
      // Lab 4 - Apply transformation to transform INP packet to EXP packet
      out_pkts = new[1];
      out_pkts[0] = new();
      out_pkts[0].kind    = cpu_trans::kind_e'(in_pkt.kind);
      out_pkts[0].address = in_pkt.address;
      out_pkts[0].data    = in_pkt.data;
      //decoding logic has to be added
   endfunction

  virtual function bit compare(cpu_trans actual, cpu_trans expected);
	 // Lab 4 - Override the scoreboard function to compare the address and data fields.
     if (actual.kind == cpu_trans::WRITE) begin
        return (1);
     end
     else begin
        `vmm_note(log, $psprintf("READ @0x%x  data=0x%x", actual.address, actual.data));
        return ((actual.kind == expected.kind) && (actual.data == expected.data));
     end
  endfunction

endclass
