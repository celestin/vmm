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
   this.sigs = cpu_port.sigs;
endfunction

task cpu_driver::write_op(cpu_trans tr);
   // Lab 2a - Drive logic for WRITE operation
   repeat (tr.trans_delay) @(sigs.cb);
   sigs.cb.busAddr <= tr.address;
   sigs.cb.busData <= tr.data; 
   sigs.cb.busRdWr_N <= 1'b0; 
   sigs.cb.adxStrb <= 1'b1; 
   @(sigs.cb);
   sigs.cb.busRdWr_N <= 1'b1; 
   sigs.cb.busData <= 'z;
   sigs.cb.adxStrb <= 1'b0;    
   repeat (4) @(sigs.cb);
endtask

task cpu_driver::read_op(cpu_trans tr);
   // Lab 2a - Drive logic for READ operation
   repeat (tr.trans_delay) @(sigs.cb);
   sigs.cb.busAddr <= tr.address;
   sigs.cb.busRdWr_N <= 1'b1;
   sigs.cb.adxStrb <= 1'b1; 
   @(sigs.cb);
   sigs.cb.adxStrb <= 1'b0;
   repeat (3) @(sigs.cb);
   tr.data = sigs.cb.busData;
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
         // Lab 2a - Call the method to implement the WRITE transaction
         tr.display("cpu_driver driving a WRITE ");
         write_op(tr);
         count++;
      end
      if (tr.kind == cpu_trans::READ) begin
         // Lab 2a - Call the method to implement the READ transaction
         tr.display("cpu_driver driving a READ ");
         read_op(tr);
         tr.display("cpu_driver received a READ request data ");
         count++;
      end
      if (count==stop_after_n_insts) break;
   end : w0
endtask
