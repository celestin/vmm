class memsys_xactor extends vmm_unit;
   memsys_trans_channel genToXtr_chan;
   cpu_trans_channel    xtrToCPU0Drv_chan;
   cpu_trans_channel    xtrToCPU1Drv_chan;
   memsys_trans  mem_tr;

   function new(string name, string inst,
                vmm_unit parent=null
               );
      super.new(name, inst, parent);
   endfunction

   task run_ph();
      fork
      while (1) begin
         genToXtr_chan.peek(mem_tr);
         genToXtr_chan.get(mem_tr);
         
         
         case(mem_tr.cpuid)
            0: xtrToCPU0Drv_chan.put(mem_tr);
            1: xtrToCPU1Drv_chan.put(mem_tr);
            default: `vmm_error(log, "illegal CPU Id generated");
         endcase
      end
      join_none
      #10;
   endtask
endclass
