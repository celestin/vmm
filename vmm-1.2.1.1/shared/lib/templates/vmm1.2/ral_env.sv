//
// Template for VMM-compliant RAL-based verification environment
// <VNAME>     Name of the vip
// <ENV>       Name of Environment class
// <CFG>       Name of the configuration class
// <IF>        Name of Interface
// <TR>        Name of the transaction descriptor
// <XACT>      Name of RAL access transactor
// <SB>        Name of vmm_sb_ds Scoreboard Class
// <MON>       Name of the monitor class
// <COV>       Name of the coverage class
// [filename]  VNAME_ral_ENV
//

`ifndef VNAME_RAL_env__SV
`define VNAME_RAL_env__SV

`include "VNAME.sv"
SING_DM_START
`include "XACT_ral.sv"
SING_DM_END
MULT_DM_START
//ToDo : Include other RAL BFM files, if more than two domains are used.
`include "XACT_DN1_ral.sv"
`include "XACT_DN2_ral.sv"
MULT_DM_END
`include "ral_VNAME.sv"
SCB_INT_MTHD_FIVE_START


class sb_notify_cb extends vmm_notify_callbacks;

   `vmm_typename(sb_notify_cb)
   SB sb;
   function new(SB sb);
      this.sb = sb;
   endfunction
   virtual function void indicated(vmm_data status);
      vmm_data cpy = status.copy();
      this.sb.insert(cpy);
   endfunction
endclass: sb_notify_cb
SCB_INT_MTHD_FIVE_END


class ENV extends vmm_ral_env;

   `vmm_typename(ENV)
   CFG cfg;
   SB sb;
   ral_block_VNAME ral_model;
   MULT_DM_START
   //ToDo : Instantiate other RAL BFMs, if more than two domains are used.
   XACT_DN1_ral DN1_host;
   XACT_DN2_ral DN2_host;
   MULT_DM_END
   SING_DM_START
   XACT_ral host;
   SING_DM_END
   SING_DRV_START
   virtual IF intf_inst;
   SING_DRV_END
   MULT_DRV_START
   virtual IF intf_inst[INTF_COUNT];
   MULT_DRV_END
   TR_channel gen2src_chan;
   TR_channel mon_chan;
   //TR_scenario_gen gen_s; // ToDo: Check Scenario generator required or not.
   TR_atomic_gen gen;
   MS_GEN_START
   TR1_channel TR1_chan;
   TR2_channel TR2_chan;
   vmm_ms_scenario_gen gen_ms;
   VNAME_ms_scen ms_scn;
   MS_GEN_END
   SING_DRV_START
   XACT driver;  
   SING_DRV_END
   MULT_DRV_START
   //Multiple drivers instantiation.
   XACT_1 driver;  
   //ToDo: Instantiate other drivers here. 
   MULT_DRV_END
   MON monitor;   
   COV cov;
   MON_2cov_connect mon2cov;
   TR_gen_sb_cb gen_sb_cb;
   PERF_START

   TR_gen_perf_cb gen_perf_cb;
   vmm_sql_db_ascii gen_perf_db;
   vmm_perf_analyzer gen_perf_an;
   vmm_sql_db_ascii driver_perf_db;
   vmm_perf_analyzer driver_perf_an;
   SING_DRV_START
   XACT_perf_cb driver_perf_cb;
   SING_DRV_END
   MULT_DRV_START
   XACT_1_perf_cb driver_perf_cb;
   //ToDo: Instantiate other drivers callbacks here. 
   MULT_DRV_END
   PERF_END
   SCB_INT_MTHD_ONE_START

   MON_sb_cb mon_sb_cb;
   SCB_INT_MTHD_ONE_END
   MACRO_START

    // ToDo: Add required vmm env member
   `vmm_env_member_begin(ENV)
       MULT_DM_START
      `vmm_env_member_xactor(DN1_host, DO_ALL)
      `vmm_env_member_xactor(DN2_host, DO_ALL)
       MULT_DM_END
       SING_DM_START
      `vmm_env_member_xactor(host, DO_ALL)
       SING_DM_END
      `vmm_env_member_xactor(gen, DO_ALL)
      `vmm_env_member_xactor(driver, DO_ALL)
      `vmm_env_member_xactor(monitor, DO_ALL)
      `vmm_env_member_channel(gen2src_chan, DO_ALL)
      `vmm_env_member_channel(mon_chan, DO_ALL)
   
   `vmm_env_member_end(ENV)
    
   MACRO_END
   extern function new(
                       SING_DRV_START
                       virtual IF intf_inst
                       SING_DRV_END
                       MULT_DRV_START
                       virtual IF intf_inst[INTF_COUNT]
                       MULT_DRV_END
                       );
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task hw_reset();
   extern virtual task cfg_dut();
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   extern virtual task wait_for_end();
   extern virtual task cleanup();
   extern virtual task report();
   MACRO_START
   SCB_INT_MTHD_THREE_START
   extern virtual task do_start();
   SCB_INT_MTHD_THREE_END
   SCB_INT_MTHD_FOUR_START
   extern virtual task do_start();
   SCB_INT_MTHD_FOUR_END
   MACRO_END
   extern virtual task start_record_replay(vmm_channel chan, int i);
endclass: ENV


function ENV::new(
                  SING_DRV_START
                  virtual IF intf_inst
                  SING_DRV_END
                  MULT_DRV_START
                  virtual IF intf_inst[INTF_COUNT]
                  MULT_DRV_END
                 );
   super.new();
   // Save a copy of the virtual interfaces
   this.intf_inst = intf_inst;
   this.cfg = new;
   $timeformat(-9, 0, "ns", 1);

   this.ral_model = new();
   super.ral.set_model(this.ral_model);

endfunction: new


function void ENV::gen_cfg();
   MACRO_START
   string md;
   MACRO_END
   super.gen_cfg();
   if (!this.cfg.randomize()) begin
      `vmm_fatal(log, "Failed to randomize test configuration");
   end
   MACRO_START
   md = vmm_opts::get_string("MODE", "NORMAL", "Specifies the mode");
   case (md)
     "NORMAL"   : cfg.mode = CFG::NORMAL;
     "RECORD"   : cfg.mode = CFG::RECORD;
     "PLAYBACK" : cfg.mode = CFG::PLAYBACK;
   endcase
   cfg.num_trans = vmm_opts::get_int("NUM_TRANS", cfg.num_trans, "Num Of transactions");
   MACRO_END

endfunction: gen_cfg


function void ENV::build();
   super.build();
   // ToDo : Add appropriate argument in new() where allocating memory to component.
   MS_GEN_START
   gen_ms = new("Multistream Scenario Gen", 2);
   ms_scn = new();
   TR1_chan = new("TR1_channel_c","channel");
   TR2_chan = new("TR2 channel_c","channel");
   gen_ms.register_channel("TR1_scenario_channel", TR1_chan);
   gen_ms.register_channel("TR2_scenario_channel", TR2_chan);
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   MS_GEN_END
   gen2src_chan = new("TR_channel_c", "gen2src_chan");
   mon_chan     = new("TR_channel_c", "mon_chan");
   gen          = new("gen", 1, gen2src_chan);
   SING_DRV_START
   driver       = new("driver", 1, intf_inst, ,gen2src_chan); 
   monitor      = new("monitor", 1, intf_inst, ,mon_chan); 
   SING_DRV_END
   MULT_DRV_START
   //ToDo: Call new for other drivers if multiple drivers are used
   driver       = new("driver", 1, intf_inst[0], ,gen2src_chan); 
   monitor      = new("monitor", 1, intf_inst[0], ,mon_chan); 
   // ToDo : Add required instance of driver/monitor 
   MULT_DRV_END
   cov          = new;
   mon2cov      = new(cov);
   monitor.append_callback(mon2cov);
   gen.stop_after_n_insts = cfg.num_trans;
   
   PERF_START

   this.gen_perf_db = new("Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   gen_perf_an  = new("perf_an",this.gen_perf_db, , , );
   gen_perf_cb  = new(gen_perf_an);
   
   this.driver_perf_db = new("Driver Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   driver_perf_an = new("driver_perf_an",this.driver_perf_db,,);
   driver_perf_cb = new(driver_perf_an);

   begin
      TR pkt = new();
      // ToDo: Add the shceme in create_table for generator
      vmm_sql_table gen_perf_tbl = gen_perf_db.create_table("TR", "");

      // ToDo: Insert the data string as per given scheme in create_table() instead of null string
      gen_perf_tbl.insert(" ");
      gen_perf_db.commit();
      gen.append_callback(gen_perf_cb);
   end

   begin
      // ToDo: Add the shceme in create_table for driver
      // ToDo: Add table for other drivers, in case of multiple drivers
      vmm_sql_table driver_perf_tbl = driver_perf_db.create_table("XACT", "");

      // ToDo: Insert the data string as per given scheme in create_table()
      driver_perf_tbl.insert(" ");
      driver_perf_db.commit();
      driver.append_callback(driver_perf_cb);
   end
   PERF_END
   
   sb        = new("SCBD");
   gen_sb_cb = new(sb);
   gen.append_callback(gen_sb_cb);
   // ToDo: Register any required callbacks
   
   SCB_INT_MTHD_ONE_START
   begin
      mon_sb_cb = new(sb);
      monitor.append_callback(mon_sb_cb);
   end
   SCB_INT_MTHD_ONE_END
   SCB_INT_MTHD_TWO_START
   this.monitor.register_vmm_sb_ds(this.sb,vmm_sb_ds::EXPECT);

   SCB_INT_MTHD_TWO_END
   SCB_INT_MTHD_FIVE_START
   begin
      sb_notify_cb mon_sb_cb = new(this.sb); 
      this.monitor.notify.append_callback(MON::OBSERVED, mon_sb_cb);
   end
   SCB_INT_MTHD_FIVE_END
   SCB_INT_MTHD_SIX_START
   this.monitor.notify.register_vmm_sb_ds(MON::OBSERVED,
                                          this.sb, vmm_sb_ds::EXPECT,
                                          vmm_sb_ds::IN_ORDER);
   SCB_INT_MTHD_SIX_END
   `vmm_note(this.log, this.cfg.psdisplay());
   MULT_DM_START
   this.DN1_host = new("RAL DN1 BFM",0,driver);
   super.ral.add_xactor(this.DN1_host);
   this.DN2_host = new("RAL DN2 BFM",0,driver);
   super.ral.add_xactor(this.DN2_host);
   MULT_DM_END
   SING_DM_START
   SING_DRV_START
   this.host = new("RAL BFM",0,intf_inst);
   SING_DRV_END
   MULT_DRV_START
   this.host = new("RAL BFM",0,intf_inst[0]);
   MULT_DRV_END 
   super.ral.add_xactor(this.host);
   SING_DM_END

   // ToDo: Instantiate transactors, using XMRs to access interface instances
   // ToDo: Register any required callbacks

endfunction: build


task ENV::reset_dut();
   super.reset_dut();

   // ToDo: Apply hardware reset to DUT
endtask: reset_dut


task ENV::hw_reset();

   // ToDo: Apply hardware reset to DUT
endtask: hw_reset

   
task ENV::cfg_dut();
   super.cfg_dut();

   // ToDo: Configure DUT
endtask: cfg_dut
NORMAL_START


task ENV::start();
   super.start();
   MS_GEN_START
   gen_ms.start_xactor();
   gen_ms.stop_after_n_scenarios = 3; 
   MS_GEN_END
   gen.start_xactor();
   SING_DRV_START
   driver.start_xactor();
   monitor.start_xactor();
   SING_DRV_END
   MULT_DRV_START
   begin
      //`foreach_vmm_xactor(XACT_1, "/./", "/./") begin
      //xact.start_xactor();
      //end
   end
   MULT_DRV_END
   this.end_vote.register_notification(this.gen.notify,TR_atomic_gen::DONE);
   this.end_vote.register_channel(this.gen2src_chan);
   this.end_vote.register_channel(this.mon_chan);
   this.end_vote.register_xactor(this.driver);

   SCB_INT_MTHD_THREE_START
   fork
      forever begin
         TR tr;
         this.monitor.out_chan.get(tr);
         this.sb.expect_in_order(tr);
      end
   join_none
   SCB_INT_MTHD_THREE_END
   SCB_INT_MTHD_FOUR_START
   fork
      forever begin
         // ToDo: OBSERVED enum should exist in monitor class
         this.monitor.notify.wait_for(MON::OBSERVED); 
         this.sb.expect_in_order(
         this.monitor.notify.status(MON::OBSERVED));
      end
   join_none
   SCB_INT_MTHD_FOUR_END
   MS_GEN_START
   fork
      forever begin
         TR1 TR1_obj;
         TR1_chan.get(TR1_obj);
         TR1_obj.display("TR1: ");
      end
      forever begin
         TR2 TR2_obj;
         TR2_chan.get(TR2_obj);
         TR2_obj.display("TR2: ");
      end
   join_none
   MS_GEN_END

  // ToDo: Start all transactors

endtask: start


task ENV::stop();
   super.stop();

   // ToDo: Stop all generators
   gen.stop_xactor();
   driver.stop_xactor();
   monitor.stop_xactor();
   // ToDo: Let the DUT drain of all pending data
endtask: stop
NORMAL_END
MACRO_START
SCB_INT_MTHD_THREE_START


task ENV::do_start();

   fork
      forever begin
         TR tr;
         this.monitor.out_chan.get(tr);
         this.sb.expect_in_order(tr);
   end
   join_none
   MULT_DRV_START
   begin
      //`foreach_vmm_xactor(XACT_1, "/./", "/./") begin
      //xact.start_xactor();
      //end
   end
   MULT_DRV_END
   // ToDo: Start all transactors

endtask: do_start
SCB_INT_MTHD_THREE_END
SCB_INT_MTHD_FOUR_START


task ENV::do_start();

   fork
      forever begin

      //ToDo: OBSERVED enum should exist in monitor class
         this.monitor.notify.wait_for(MON::OBSERVED); 
         this.sb.expect_in_order(
         this.monitor.notify.status(MON::OBSERVED));
      end
   join_none
   MULT_DRV_START
   begin
      //`foreach_vmm_xactor(XACT_1, "/./", "/./") begin
      //xact.start_xactor();
      //end
   end
   MULT_DRV_END
   // ToDo: Start all transactors

endtask: do_start
SCB_INT_MTHD_FOUR_END
MACRO_END

// If mode is set to RECORD mode, transaction information is 
// dumped in a file. If mode is set to PLAYBACK mode, transaction 
// information is loaded from the file.
task ENV::start_record_replay(vmm_channel chan, int i);
   fork begin
      string id_s = $psprintf("%0d", i);
      if (cfg.mode == CFG::RECORD) begin
         chan.record({"Chan", id_s, ".dat"});
      end
      else if (cfg.mode == CFG::PLAYBACK) begin
         bit success;
         TR tr = new;
         chan.playback(success, {"Chan", id_s, ".dat"}, tr);
         if (!success) begin
            `vmm_error(log, {"Playback mode failed for channel", id_s});
         end
      end
   end
   join_none
endtask: start_record_replay


task ENV::wait_for_end();
   super.wait_for_end();
   this.end_vote.wait_for_consensus();
   // ToDo: Figure out when it is time to end the test
endtask: wait_for_end


task ENV::cleanup();
   super.cleanup();
   // ToDo: check that nothing was lost

endtask: cleanup


task ENV::report() ;
   super.report();
   PERF_START
   this.gen_perf_an.save_db();
   this.gen_perf_an.report();
   this.driver_perf_an.save_db();
   this.driver_perf_an.report();
   PERF_END
   sb.report();
   // ToDo: Generate the Final Report

endtask: report

`endif // VNAME_RAL_env__SV
