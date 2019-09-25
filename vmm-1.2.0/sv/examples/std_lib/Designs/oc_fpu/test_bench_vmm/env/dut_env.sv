/***************************************************************************
*******************************************************************************
*
* Basic Transaction Verification Module aimed at
* creating transactions based on Floating point unit from Open cores
*
*******************************************************************************
*/

`ifndef _DUT_ENV_SV_
`define _DUT_ENV_SV_

typedef class scoreboard;
typedef class coverage_model;

// Integrate scoreboard in the monitor callback structure
class fpu_mon_callbacks_scoreboarding extends fpu_mon_callbacks ;

   local scoreboard sb;
   
   function new(scoreboard sb) ;
      this.sb = sb;
   endfunction: new
   
   virtual task post_mon(fpu_mon   mon,
                         fpu_result rslt,
                         ref bit          drop) ;

      rslt.display("In Sb: Observed result:");

      this.sb.compare_result(rslt);
      drop = 1; //only callbacks are used for sending the result to here
      //so to disable the result addition to channel drop is set to 1
      //Note: if the monitor had been configured with is_sink == 1, this 
      //  step is not necessary.
   endtask: post_mon
endclass: fpu_mon_callbacks_scoreboarding

class fpu_master_callbacks_scoreboarding extends fpu_master_callbacks ;

    local scoreboard sb;
    local coverage_model cm;

    function new(scoreboard sb,
                 coverage_model cm) ;
      this.sb = sb;
      this.cm = cm;
    endfunction: new

    virtual task post_trans(fpu_master master,
                             fpu_trans  tr) ;
        this.cm.cover_this(tr);
        this.sb.calculate_result(tr);
   endtask: post_trans
endclass: fpu_master_callbacks_scoreboarding

class env extends vmm_env ;

  test_cfg          cfg;   // Test config

  virtual fpu_i.STB  iport; //interface to DUT

  fpu_gen    gen;   // Transaction generator
  fpu_master mst;   // Transactor
  fpu_mon    mon;   // Monitor

  scoreboard        sb;
  coverage_model    cm;

  bit end_simulation;
  event end_simulation_event;
  
  function new(virtual fpu_i.STB iport);
     super.new();
     this.cfg = new;
     this.iport = iport;
  endfunction: new

  virtual function void gen_cfg() ;
    super.gen_cfg();
    void'(this.cfg.randomize());
  endfunction: gen_cfg

  virtual function void build() ;
    super.build();

    this.mst = new("mst", 0, this.iport, this.cfg.fpu);
    this.mon = new("mon", 0, this.iport);
    this.gen = new("gen", 0, this.mst.in_trans);

    this.sb = new(this.cfg);
    this.cm = new;
    //ToDo: check the order of registration of callbacks
    begin
       fpu_mon_callbacks_scoreboarding cb1 = new(this.sb);
       this.mon.append_callback(cb1);
    end
    begin
       fpu_master_callbacks_scoreboarding cb2 = new(this.sb, this.cm);
       this.mst.append_callback(cb2);
    end
  endfunction: build

  virtual task cfg_dut() ;
    super.cfg_dut();
  endtask: cfg_dut

  virtual task reset_dut() ;
      super.reset_dut();
      `vmm_note(this.log,"No reset in the DUT Spec !?");
  endtask: reset_dut

  virtual task start() ;
    super.start();
    gen.stop_after_n_scenarios = this.cfg.run_for;
    gen.start_xactor();
    mst.start_xactor();
    mon.start_xactor();
    
    // End the simulation ASAP after finishing default behavior
    end_simulation = 1; 
    ->end_simulation_event;
  endtask: start

  virtual task wait_for_end() ;
     super.wait_for_end();

     // Wait for the generator to be done
     gen.notify.wait_for(vmm_xactor::XACTOR_STOPPED);

     // Wait for a confirmation of the end of simulation
     //ToDo: fix with a wait
     while (this.end_simulation == 0) 
        @(this.end_simulation_event);

     // Then wait for the master to complete the last transaction
     while (mst.in_trans.level() > 0) begin
        mst.notify.wait_for(mst.TRANS_DONE);
     end

     // Wait some more to make sure the monitor reports the last
     // transaction that just completed
     //##5;
     repeat (5) @(this.iport.cb);
  endtask: wait_for_end

  virtual task stop() ;
    super.stop();
    gen.stop_xactor();
  endtask: stop

  virtual task report() ;
     super.report();
  endtask: report
endclass: env

`endif
