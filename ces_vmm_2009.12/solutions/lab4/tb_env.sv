`ifndef TB_ENV__SV
`define TB_ENV__SV

`include "test_cfg.sv"
`include "Packet.sv"
`include "GenCovCallbacks.sv"
`include "scoreboard.sv"
`include "GenSbCallbacks.sv"

// Lab 4 - Add include statement for Driver.sv, Receiver.sv and RcvSbCallbacks.sv
// ToDo
`include "Driver.sv"
`include "Receiver.sv"
`include "RcvSbCallbacks.sv"


class tb_env extends vmm_env;
   test_cfg cfg;
   Packet blueprint;

   // Second part of Lab 4 (scenario generator) - Replace atomic_gen with scenario_gen
   // ToDo
   Packet_scenario_gen gen;


   GenCovCallbacks gen_cov_cb;
   scoreboard sb;
   GenSbCallbacks gen_sb_cb;

   // Lab 4 - Access DUT physcial signal via DUT interface
   // ToDo
   virtual router_io sigs = test_dut_top.sigs;


   // Lab 4 - Instantiate vmm_broadcast, Driver, Receiver and RcvSbCallbacks components
   // ToDo
   vmm_broadcast  bcast;
   Driver         drv[$];
   Receiver       rcv[$];
   RcvSbCallbacks rcv_sb_cb;

   `vmm_env_member_begin(tb_env)
      `vmm_env_member_xactor(gen, DO_ALL)
      `vmm_env_member_xactor(bcast, DO_ALL)
      `vmm_env_member_xactor_array(drv, DO_ALL)
      `vmm_env_member_xactor_array(rcv, DO_ALL)
   `vmm_env_member_end(tb_env)
    
   extern function new();
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   extern virtual task wait_for_end();
   extern virtual task cleanup();
   extern virtual task report();
endclass: tb_env

function tb_env::new();
   super.new();
   cfg = new();
endfunction: new

function void tb_env::gen_cfg();
   super.gen_cfg();
   if (!cfg.randomize())
      `vmm_fatal(log, "Test Configuration Failed Randomization");
   `vmm_note(log, cfg.psdisplay());
endfunction: gen_cfg

function void tb_env::build();
   super.build();
   this.gen = new("gen", 0);
   this.gen.stop_after_n_insts = this.cfg.run_for_n_packets;
   this.blueprint = new();
   this.blueprint.valid_sa = this.cfg.iports_in_use.find_index() with (item == 1);
   this.blueprint.valid_da = this.cfg.oports_in_use.find_index() with (item == 1);

   // Second part of Lab 4 (scenario generator) - Replace using in scenario_set instead of randomized_obj
   // ToDo
   foreach (this.gen.scenario_set[i]) begin
      this.gen.scenario_set[i].using = this.blueprint;
   end
   this.gen_cov_cb = new();
   this.gen.append_callback(gen_cov_cb);
   this.sb = new(this.cfg);
   this.gen_sb_cb = new(this.sb);
   this.gen.append_callback(gen_sb_cb);

   // Lab 4 - Construct the vmm_broadcast object and connect to gen.out_chan
   // ToDo
   this.bcast = new("Gen to Driver Broadcast", "bcast", gen.out_chan);


   // Lab 4 - Construct drivers in use and connect to generator via vmm_broadcast
   // ToDo
   foreach (this.cfg.iports_in_use[i]) begin
      if (this.cfg.iports_in_use[i]) begin
         Driver d = new($psprintf("Driver_%0d", i), i, this.sigs);
         this.bcast.new_output(d.in_chan);
         this.drv.push_back(d);
      end
   end


   // Lab 4 - Construct receivers in use, append the scoreboard callbacks and drain the out_chan
   // ToDo
   this.rcv_sb_cb = new(this.sb);
   foreach (this.cfg.oports_in_use[i]) begin
      if (this.cfg.oports_in_use[i]) begin
         Receiver r = new($psprintf("Receiver_%0d", i), i, this.sigs);
         r.append_callback(rcv_sb_cb);
         r.out_chan.sink();
         this.rcv.push_back(r);
      end
   end



endfunction: build

task tb_env::reset_dut();
   super.reset_dut();
   // Lab 4 - Implement the reset protocol
   // ToDo
   this.sigs.reset_n <= 1'b0;
   this.sigs.mclk.frame_n <= '1;
   this.sigs.mclk.valid_n <= '1;
   this.sigs.mclk.din <= '1;
   ##2 this.sigs.mclk.reset_n <= 1'b1;
   repeat(15) @(this.sigs.mclk);
endtask: reset_dut
   
task tb_env::cfg_dut();
   super.cfg_dut();
endtask: cfg_dut

task tb_env::wait_for_end();
   super.wait_for_end();

   // lab 4 - Wait for scoreboard's DONE flag instead of generator's flag
   // ToDo
   this.sb.notify.wait_for(sb.DONE);


endtask: wait_for_end

task tb_env::cleanup();
   super.cleanup();
endtask: cleanup

task tb_env::report() ;
   super.report();
   `vmm_note(log, this.cfg.psdisplay());
   this.sb.report();
endtask: report

`endif // TB_ENV__SV
