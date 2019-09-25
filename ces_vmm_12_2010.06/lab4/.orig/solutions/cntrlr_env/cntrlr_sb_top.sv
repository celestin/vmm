// Lab 4 - Include the scoreboard class
`include "cntrlr_sb.sv"

class cntrlr_sb_top extends vmm_xactor;

   // Lab 4 - Use `vmm_tlm_analysis_export shorthand macro to create unique names for TLM analysis ports
   `vmm_tlm_analysis_export(_cpu_trans_started)
   `vmm_tlm_analysis_export(_cpu_trans_ended)
   `vmm_tlm_analysis_export(_sram)
   
   // Lab 4 - Declare instances of analysis export objects and construct them
   vmm_tlm_analysis_export_cpu_trans_started  #(cntrlr_sb_top, cpu_trans) cpu_start_export = new(this, "CpuAnPort", 10, 0);
   vmm_tlm_analysis_export_cpu_trans_ended  #(cntrlr_sb_top, cpu_trans) cpu_end_export = new(this, "CpuAnPort", 10, 0);
   vmm_tlm_analysis_export_sram #(cntrlr_sb_top, sram_trans) sram_export = new(this, "SramAnPort", 10, 0);

   // Optional - Create a vmm_tr_stream for cpu_trans
   vmm_tr_stream cpu_stream;

   cpu2sram_sb cpu2sram;
   sram2cpu_sb sram2cpu;
   
   int addr_wdth, num_sram_devices;

   function new(string inst="",vmm_object parent = null, int num_sram_devices, int addr_wdth);
      super.new(get_typename(),inst,0,parent);
      this.num_sram_devices = num_sram_devices;
      this.addr_wdth = addr_wdth;
   endfunction

   function void build_ph();
      cpu2sram = new("CPU->SRAM", num_sram_devices);
      sram2cpu = new("SRAM->CPU", num_sram_devices);

      // Optional - Open the cpu_stream
      cpu_stream = vmm_tr_record::open_stream("cpu_stream", "cpu_trans", vmm_debug::NORMAL_SEV);
   endfunction

   function int get_stream_id(bit [31:0] addr);
      if (num_sram_devices == 1) return 0;
      if (num_sram_devices == 2) return addr[addr_wdth];
      if (num_sram_devices == 4) 
      begin
         if (addr_wdth == 8) return addr[9:8];
         if (addr_wdth == 9) return addr[10:9];
         if (addr_wdth == 10) return addr[11:10];
      end
   endfunction

   function void write_cpu_trans_started(int id=-1, cpu_trans tr);
      `vmm_trace(log, tr.psdisplay("@CPU Trans Started "));

      // Optional - start capture of cpu_stream
      vmm_tr_record::start_tr(cpu_stream, "Transaction Start", tr.psdisplay());

      // Lab4 - Insert the cpu_trans packet at the CPU side at the start of the CPU transaction drive
      cpu2sram.inp_insert(tr,.exp_stream_id(get_stream_id(tr.address)));
   endfunction

   function void write_cpu_trans_ended(int id=-1, cpu_trans tr);
      `vmm_trace(log, tr.psdisplay("@CPU Trans Completed "));

      // Optional - end capture of cpu_stream
      vmm_tr_record::end_tr(cpu_stream);

      // Lab 4 - Expect the cpu_trans packet at the SRAM side at the end of the CPU transaction drive
      sram2cpu.expect_in_order(tr, .inp_stream_id(get_stream_id(tr.address)));
   endfunction

   function void write_sram(int id=-1, sram_trans tr);
      `vmm_trace(log, tr.psdisplay("@SRAM Trans "));
      // Lab 4 - On receiving a packet at the SRAM side do a insert() at the SRAM side and at the same 
      //         call an expect of the received packet on the CPU side.
      sram2cpu.inp_insert(tr, .inp_stream_id(id));
      cpu2sram.expect_out_of_order(tr, .exp_stream_id(id));
   endfunction

   function void final_ph();
      // Optional - Close the cpu_stream
      // ToDo
      vmm_tr_record::close_stream(cpu_stream);
   endfunction

endclass
