`include "vmm_sb.sv"

class cpu2sram_sb extends vmm_sb_ds_typed#(cpu_trans, sram_trans);

   function new(string inst, int num_sram_devices);
      super.new(inst);

      // Lab 4 - Define streams based on how many logical INPUT and OUTPUT streams there are
      // ToDo

   endfunction

   virtual function bit transform(input cpu_trans in_pkt, output sram_trans out_pkts[]);

      // Lab 4 - Apply transformation to transform INP packet to EXP packet
      // ToDo

   endfunction

   virtual function bit compare(sram_trans actual, sram_trans expected);

      // Lab 4 - Override the scoreboard function to compare the address and data fields.
      // ToDo

   endfunction

endclass


class sram2cpu_sb extends vmm_sb_ds_typed#(sram_trans, cpu_trans);

   function new(string inst, int num_sram_devices);
      super.new(inst);

      // Lab 4 - Define streams based on how many logical INPUT and OUTPUT streams there are
      //ToDo

   endfunction

   virtual function bit transform(input sram_trans in_pkt, output cpu_trans out_pkts[]);

      // Lab 4 - Apply transformation to transform INP packet to EXP packet
      // ToDo

   endfunction

  virtual function bit compare(cpu_trans actual, cpu_trans expected);

     // Lab 4 - Override the scoreboard function to compare the address and data fields.
     // ToDo

  endfunction

endclass
