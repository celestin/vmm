
typedef class cpu_driver;

class cpu_driver_callbacks extends vmm_xactor_callbacks;
    virtual task pre_trans  (cpu_driver driver,
                               cpu_trans tr,
                               bit drop);
    endtask


   virtual task post_trans  (cpu_driver driver,
                               cpu_trans tr
                               );
   endtask
endclass

class cpu_driver extends vmm_unit;
`vmm_typename(cpu_driver)
  virtual cpu_if.drvprt  iport;
  cpu_trans_channel in_chan;
  cpuport iport_obj;

  extern function new(string name, string inst,
                      vmm_unit parent=null
                     );
  extern task run_ph();
  extern task write_op(cpu_trans tr);
  extern task read_op(cpu_trans tr);
  extern virtual function void connect_ph();
  extern virtual function void start_of_sim_ph();
endclass

function cpu_driver::new(string name, string inst,
                         vmm_unit parent 
                        );
  super.new(name, inst, parent);
endfunction

task cpu_driver::run_ph();
  cpu_trans   tr;
  `vmm_trace(log, $psprintf("... Running phase %M"));

  fork 
    while (1) begin : w0
      this.in_chan.peek(tr);
      `vmm_note (this.log, $psprintf ("Driver received a transaction: %s", tr.psdisplay()));
      if (tr.kind == cpu_trans::WRITE) begin
        write_op(tr);
      end
      if (tr.kind == cpu_trans::READ) begin
        read_op(tr);
      end
      tr.notify.indicate(vmm_data::ENDED);
      this.in_chan.get(tr);
    end : w0
  join_none
endtask

task cpu_driver::write_op(cpu_trans tr);
    iport.cb.request <= 1'b1;
    wait (iport.cb.grant == 1'b1);
    @(iport.cb);
    iport.cb.busAddr <= tr.address;
    iport.cb.busData <= tr.data; 
    iport.cb.busRdWr_N <= 1'b0; 
    iport.cb.adxStrb <= 1'b1; 
    @(iport.cb);
    iport.cb.busRdWr_N <= 1'b1; 
    iport.cb.busData <= 8'bzzzzzzzz; 
    iport.cb.adxStrb <= 1'b0;    
    @(iport.cb);
    iport.cb.request <= 1'b0;
endtask

task cpu_driver::read_op(cpu_trans tr);
    iport.cb.request <= 1'b1;
    wait (iport.cb.grant == 1'b1);
    @(iport.cb);
    iport.cb.busAddr <= tr.address;
    iport.cb.busRdWr_N <= 1'b1;
    iport.cb.adxStrb <= 1'b1; 
    @(iport.cb);
    iport.cb.adxStrb <= 1'b0;
    repeat (tr.trans_delay) @(iport.cb);
    iport.cb.busData <= tr.data;
    @(iport.cb);
    iport.cb.request <= 1'b0;
endtask

function void cpu_driver::connect_ph();
   bit is_set;
  `vmm_trace(log, $psprintf("... Running phase %M"));

   if ($cast(iport_obj, vmm_opts::get_object_obj(is_set,this,"cpu_port"))) begin
      if (iport_obj != null)
       this.iport = iport_obj.iport;
      else
       `vmm_fatal(log, "Virtual port wrapper not initialized");
   end
endfunction

function void cpu_driver::start_of_sim_ph();
  `vmm_trace(log, $psprintf("... Running phase %M"));

   if (iport == null)
       `vmm_fatal(log, "Virtual port not connected to the actual interface instance");
endfunction

