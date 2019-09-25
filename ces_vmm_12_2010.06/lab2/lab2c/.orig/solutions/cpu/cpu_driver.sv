// Lab 2c - Create a callback class extended from vmm_xactor_callbacks.
typedef class cpu_driver;

class cpu_driver_callbacks extends vmm_xactor_callbacks;
   // Create 2 callback methods pre_trans() and post_trans()
   virtual task pre_trans(cpu_driver driver, cpu_trans tr, ref bit drop); endtask
   virtual task post_trans(cpu_driver driver, cpu_trans tr); endtask
endclass

class cpu_driver extends vmm_xactor;
   `vmm_typename(cpu_driver)
   virtual cpu_if.drvprt  sigs;
   int stop_after_n_insts;

   extern function new(string inst="", vmm_unit parent=null, int stop_after_n_insts);
   extern virtual task write_op(cpu_trans tr);
   extern virtual task read_op(cpu_trans tr);
   extern virtual protected task main();
   extern virtual function void connect_ph();
endclass

function cpu_driver::new(string inst, vmm_unit parent=null, int stop_after_n_insts);
   super.new(get_typename(), inst, 0, parent);
   this.stop_after_n_insts = stop_after_n_insts;
endfunction

task cpu_driver::write_op(cpu_trans tr);
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
   repeat (tr.trans_delay) @(sigs.cb);
   sigs.cb.busAddr <= tr.address;
   sigs.cb.busRdWr_N <= 1'b1;
   sigs.cb.adxStrb <= 1'b1; 
   @(sigs.cb);
   sigs.cb.adxStrb <= 1'b0;
   repeat (3) @(sigs.cb);
   tr.data = sigs.cb.busData;
endtask

task cpu_driver::main();
   int count = 0;
   cpu_trans   tr;
   bit drop = 0;
   super.main();
   
   while (1) begin : w0
      tr = new();
      tr.randomize();
      tr.data_id = count;
      // Lab 2c - Insert the callback hook. pre_trans() before transaction drive
      `vmm_callback(cpu_driver_callbacks, pre_trans(this, tr, drop));
      if (tr.kind == cpu_trans::WRITE) begin
         `vmm_trace(log, tr.psdisplay("cpu_driver driving a WRITE "));
         write_op(tr);
         count++;
      end
      else if (tr.kind == cpu_trans::READ) begin
         `vmm_trace(log, tr.psdisplay("cpu_driver requesting a READ "));
         read_op(tr);
         `vmm_trace(log, tr.psdisplay("cpu_driver received a READ request data "));
         count++;
      end
      // Lab 2c - Insert the callback hook. post_trans after transaction drive
      `vmm_callback(cpu_driver_callbacks, post_trans(this, tr));

      if (count==stop_after_n_insts) break;
   end : w0

   this.notify.indicate(vmm_xactor::XACTOR_IDLE);
   this.notify.reset(vmm_xactor::XACTOR_BUSY);
   this.notify.indicate(vmm_xactor::XACTOR_STOPPED);
endtask

function void cpu_driver::connect_ph();
   `vmm_note(log, "Connecting the cpu_driver to the DUT within the connect_ph()");
   this.sigs = cpu_port.sigs;
endfunction
