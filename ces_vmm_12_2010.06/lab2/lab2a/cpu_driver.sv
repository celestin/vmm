class cpu_driver;
   string inst;
   virtual cpu_if.drvprt  sigs;
   int stop_after_n_insts;

   extern function new(string inst="", int stop_after_n_insts);
   extern virtual task main();
   extern virtual task write_op(cpu_trans tr);
   extern virtual task read_op(cpu_trans tr);
endclass

function cpu_driver::new(string inst, int stop_after_n_insts);
   this.inst = inst;
   this.stop_after_n_insts = stop_after_n_insts;
  
   // Lab 2a - initialize the virtual port wrapper to connect to DUT.
   // ToDo

endfunction

task cpu_driver::write_op(cpu_trans tr);
   // Lab 2a - Drive logic for WRITE operation
   // ToDo

endtask

task cpu_driver::read_op(cpu_trans tr);
   // Lab 2a - Drive logic for READ operation
   // ToDo

endtask

// Lab 2a - complete the main thread by calling write_op() and read_op()
//          at appropriate places in the task main()
task cpu_driver::main();
   int count = 0;
   cpu_trans   tr;

   while (1) begin : w0
      tr = new();
      tr.randomize();
      tr.data_id = count;
     
      if (tr.kind == cpu_trans::WRITE) begin
         tr.display("cpu_driver driving a WRITE ");
         // Lab 2a - Call the method to implement the WRITE transaction
         // ToDo

         count++;
      end
      if (tr.kind == cpu_trans::READ) begin
         tr.display("cpu_driver driving a READ ");
         // Lab 2a - Call the method to implement the READ transaction
         // ToDo

         tr.display("cpu_driver received a READ request data ");
         count++;
      end
      if (count==stop_after_n_insts) break;
   end : w0
endtask
