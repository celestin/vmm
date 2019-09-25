/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`include "Configuration.sv"
`include "Packet.sv"
`include "Scoreboard.sv"
`include "Driver.sv"
`include "DriverCovCallbacks.sv"
`include "DriverSbCallbacks.sv"
`include "Receiver.sv"
`include "ReceiverCovCallbacks.sv"

class Environment extends vmm_env;
  vmm_version          vmm_ver;
  Configuration        cfg;
  Packet_atomic_gen    gen[];
  Scoreboard           sb;
  Driver               drv[];
  DriverCovCallbacks   drv_cov_cb;
  DriverSbCallbacks    drv_sb_cb;
  Receiver             rcv[];
  ReceiverCovCallbacks rcv_cov_cb;

  virtual router_io.TB router;
  function new(virtual router_io.TB router);
     super.new("Environment");
     this.router = router;
     cfg = new();
  endfunction

  virtual function void gen_cfg();
     super.gen_cfg();
     if (!cfg.randomize()) `vmm_fatal(this.log, "Configuration Randomization Failed!\n");
  endfunction

  virtual function void build();
     super.build();
     vmm_ver = new();
     vmm_ver.display("**** Note : ");
     gen = new[16];
     sb = new("sb");
     drv = new[16];
     rcv = new[16];
     drv_cov_cb = new("DrvCov", this);
     drv_sb_cb = new(sb, "DrvSb", this);
     rcv_cov_cb = new("RcvCov", this);
     for(int i=0; i<drv.size; i++) begin
        drv[i] = new($psprintf("Driver[%0d]", i), i, router);
        gen[i] = new($psprintf("Gen[%0d]", i), i);
        gen[i].stop_after_n_insts = cfg.run_for_n_packets;
        gen[i].out_chan.tlm_bind(drv[i].socket,vmm_tlm::TLM_BLOCKING_PORT);
        drv[i].write_port.tlm_bind(drv_cov_cb.write_port, i);
        drv[i].write_port.tlm_bind(drv_sb_cb.write_port, i);
     end
     for(int i=0; i<rcv.size; i++) begin
        rcv[i] = new($psprintf("Receiver[%0d]", i), i, router);
        rcv[i].socket.tlm_bind(sb.socket, i);
        rcv[i].write_port.tlm_bind(rcv_cov_cb.write_port, i);
     end
  endfunction

  virtual task reset_dut();
     super.reset_dut();
     reset();
  endtask

  virtual task cfg_dut();
     super.cfg_dut();
  endtask

  virtual task start();
     super.start();
     sb.start_xactor();
     foreach(cfg.valid_iports[i]) begin
        drv[cfg.valid_iports[i]].start_xactor();
        gen[cfg.valid_iports[i]].start_xactor();
     end
     foreach(cfg.valid_oports[i])
        rcv[cfg.valid_oports[i]].start_xactor();
  endtask

  virtual task wait_for_end();
     super.wait_for_end();
     fork
        sb.notify.wait_for(sb.DONE);
     join_any
  endtask

  virtual task stop();
     super.stop();
     foreach(drv[i]) begin
        drv[i].stop_xactor();
        gen[cfg.valid_iports[i]].stop_xactor();
     end
     foreach(drv[i])
        drv[i].notify.wait_for(vmm_xactor::XACTOR_IDLE);
     foreach(rcv[i])
        rcv[i].notify.wait_for(vmm_xactor::XACTOR_IDLE);
     endtask

  virtual task cleanup();
     super.cleanup();
  endtask

  virtual task report();
     super.report();
     sb.report();
  endtask

  virtual protected task reset();
     `vmm_trace(this.log, $psprintf("%m"));
     router.reset_n <= 1'b0;
     router.cb.frame_n <= '1;
     router.cb.valid_n <= '1;
     ##2 router.cb.reset_n <= 1'b1;
     repeat(15) @(router.cb);
  endtask
endclass

