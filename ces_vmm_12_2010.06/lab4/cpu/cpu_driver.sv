typedef class cpu_driver;

class cpu_driver_callbacks extends vmm_xactor_callbacks;
   virtual task pre_trans  (cpu_driver driver,
                            cpu_trans tr,
                            ref bit drop);
   endtask

   virtual task post_trans  (cpu_driver driver,
                             cpu_trans tr);
   endtask
endclass

class cpu_driver extends vmm_xactor;
   virtual cpu_if.drvprt sigs;
   string                inst;
   cpuport               cpu_port_obj;
   cpu_trans_channel     in_chan;

   // Lab 4 - Declare instances of analysis ports to hook up the scoreboard
   // ToDo
 

   extern function new(string inst="", vmm_unit parent=null);
   extern virtual function void build_ph();
   extern virtual task write_op(cpu_trans tr);
   extern virtual task read_op(cpu_trans tr);
   extern virtual protected task main();
   extern virtual function void connect_ph();
endclass

function cpu_driver::new(string inst, vmm_unit parent=null);
   super.new("cpu_driver", inst, 0, parent);
   this.inst = inst;
endfunction

function void cpu_driver::build_ph();
   // Lab 4 - Construct the analysis ports
   // ToDo

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
   cpu_trans   tr;
   bit drop;
   super.main();
   
   while (1) begin : w0
      wait_if_stopped_or_empty(this.in_chan);
      this.in_chan.activate(tr);
      `vmm_callback(cpu_driver_callbacks, pre_trans(this, tr, drop));

      // Lab 4 - Call the pre_analysis_port.write() method before the transaction drive
      // ToDo


      if (tr.kind == cpu_trans::WRITE) begin
         `vmm_trace(log, tr.psdisplay("cpu_driver driving a WRITE "));
         write_op(tr);
      end
      if (tr.kind == cpu_trans::READ) begin
         `vmm_trace(log, tr.psdisplay("cpu_driver requesting a READ "));
         read_op(tr);
         `vmm_trace(log, tr.psdisplay("cpu_driver got READ data "));
      end
      `vmm_callback(cpu_driver_callbacks, post_trans(this, tr));

      // Lab 4 - Call the analysis_port.write() method after the transaction drive
      // ToDo 


      this.in_chan.remove();
   end : w0
endtask

function void cpu_driver::connect_ph();
   bit is_set;
   `vmm_note(log, "Connecting the cpu_driver to the DUT within the connect_ph()");
   if ($cast(cpu_port_obj, vmm_opts::get_object_obj(is_set,this,"cpu_port"))) begin
      if (cpu_port_obj != null)
         this.sigs = cpu_port_obj.sigs;
      else
         `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction
