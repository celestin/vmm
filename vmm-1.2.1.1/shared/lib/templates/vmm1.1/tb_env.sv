//
// Template for VMM-compliant verification environment
// <ENV>       Name of Environment class
// <CFG>       Name of the configuration class
// <IF>        Name of Interface
// <TR>        Name of the transaction descriptor
// <XACT>      Name of the driver
// <SB>        Name of vmm_sb_ds Scoreboard class
// <MON>       Name of the monitor class
// <COV>       Name of the coverage class
// [filename]  ENV
//

`ifndef ENV__SV
`define ENV__SV

//Including all the required component files here
`include "VNAME.sv"
//ToDo: Include required files here

SCB_INT_MTHD_FIVE_START


class sb_notify_cb extends vmm_notify_callbacks;
   SB sb;
   function new(SB sb);
      this.sb = sb;
   endfunction: new
   virtual function void indicated(vmm_data status);
      vmm_data cpy = status.copy();
      this.sb.insert(cpy);
   endfunction: indicated
endclass: sb_notify_cb
SCB_INT_MTHD_FIVE_END
RAL_START


class ENV extends vmm_ral_env;
RAL_END
COMMON_START


class ENV extends vmm_env;
COMMON_END
   CFG cfg;
   SCBD_EN_START 
   SB sb;
   SCBD_EN_END
   RAL_START
   ral_block_VNAME ral_model;
   MULT_DM_START
   //ToDo : Instantiate other RAL BFMs, if more than two domains are used.
   XACT_DN1_ral DN1_host;
   XACT_DN2_ral DN2_host;
   MULT_DM_END
   SING_DM_START
   XACT_ral host;
   SING_DM_END
   RAL_END
   // ToDo: Declare transactor instances as data members
   SING_DRV_START
   virtual IF intf_inst;
   SING_DRV_END
   MULT_DRV_START
   virtual IF intf_inst[INTF_COUNT];
   MULT_DRV_END
   TR_channel mon_chan;
   ATMC_GEN_START
   TR_channel atmc_gen2src_chan;
   TR_atomic_gen atmc_gen;
   ATMC_GEN_END
   SCN_GEN_START 
   TR_channel scen_gen2src_chan;
   TR_scenario_gen scen_gen;
   SCN_GEN_END
   MS_GEN_START
   SING_DRV_START
   TR_channel TR_chan;  
   SING_DRV_END
   MULT_DRV_START
   TR_channel TR_chan_RPTNO;  //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   //ToDo : Declare other required no. of channels here of required transaction types
   vmm_ms_scenario_gen gen_ms;
   VNAME_ms_scen ms_scn;
   MS_GEN_END
   SING_DRV_START
   XACT driver;  
   SING_DRV_END
   MULT_DRV_START
   //Multiple driver instantiation
   XACT driver_RPTNO;     //VMMGEN_RPT_ON_XACT
   //ToDo: Instantiate other drivers here. 
   MULT_DRV_END

   MON monitor;   
   COV cov;
   MON_2cov_connect mon2cov;
   SCBD_EN_START
   XACT_sb_callbacks bfm_sb_cb;
   SCBD_EN_END
   PERF_START

   MON_perf_cb monitor_perf_cb;
   vmm_sql_db_ascii monitor_perf_db;
   vmm_perf_analyzer monitor_perf_an;
   vmm_sql_db_ascii driver_perf_db;
   vmm_perf_analyzer driver_perf_an;
   SING_DRV_START
   XACT_perf_cb driver_perf_cb;
   SING_DRV_END
   MULT_DRV_START
   XACT_perf_cb driver_perf_cb_RPTNO;  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   PERF_END
   SCB_INT_MTHD_ONE_START

   MON_sb_cb mon_sb_cb;
   SCB_INT_MTHD_ONE_END
   MACRO_START

   `vmm_env_member_begin(ENV)
      RAL_START
      MULT_DM_START
      `vmm_env_member_xactor(DN1_host, DO_ALL)
      `vmm_env_member_xactor(DN2_host, DO_ALL)
       MULT_DM_END
       SING_DM_START
      `vmm_env_member_xactor(host, DO_ALL)
       SING_DM_END
      RAL_END
      // ToDo: Add required vmm env member
      ATMC_GEN_START
      `vmm_env_member_xactor(atmc_gen, DO_ALL)
      `vmm_env_member_channel(atmc_gen2src_chan, DO_ALL)
      ATMC_GEN_END
      SCN_GEN_START 
      `vmm_env_member_xactor(scen_gen, DO_ALL)
      `vmm_env_member_channel(scen_gen2src_chan, DO_ALL)
      SCN_GEN_END 
      MS_GEN_START
      `vmm_env_member_xactor(gen_ms, DO_ALL)
      MS_GEN_END
      SING_DRV_START
      `vmm_env_member_xactor(driver, DO_ALL)
      SING_DRV_END
      MULT_DRV_START
      `vmm_env_member_xactor(driver_RPTNO, DO_ALL)  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
      `vmm_env_member_xactor(monitor, DO_ALL)
      `vmm_env_member_channel(mon_chan, DO_ALL)
 
   `vmm_env_member_end(ENV)
    
   // ToDo: Add required short hand override method
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
   RAL_START
   extern virtual task hw_reset();
   RAL_END
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
   RAL_START
   this.ral_model = new();
   super.ral.set_model(this.ral_model);
   RAL_END
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

   MS_GEN_START
   gen_ms = new("Multistream Scenario Gen", 2);
   ms_scn = new();
   SING_DRV_START
   TR_chan = new("TR channel_c","channel");    
   gen_ms.register_channel("TR_scenario_channel", TR_chan);  
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR channel_cRPTNO","channel_RPTNO");    //VMMGEN_RPT_ON_TR
   gen_ms.register_channel("TR_scenario_channel_RPTNO", TR_chan_RPTNO); //VMMGEN_RPT_ON_TR 
   MULT_DRV_END
   //ToDo : Instantiate other required channels of required transaction types and register them 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   //ToDo: Register required scenarios
   MS_GEN_END
   mon_chan = new("Mon_TR_channel_c", "mon_chan");
   ATMC_GEN_START
   // ToDo : Add appropriate argument in new() where allocating memory to component.
   atmc_gen2src_chan = new("TR_atomic_channel_c", "atmc_gen2src_chan");
   atmc_gen          = new("atomic_gen", 1, atmc_gen2src_chan);
   ATMC_GEN_END
   SCN_GEN_START
   // ToDo : Add appropriate argument in new() where allocating memory to component.
   scen_gen2src_chan = new("TR_scenario_channel_c", "scen_gen2src_chan");
   scen_gen          = new("scenario_gen", 1, scen_gen2src_chan);
   SCN_GEN_END
   FD_DRIV_START 
   SING_DRV_START
   FULL_DUPLEX_PHY_BFM_START
	ATMC_GEN_START
   driver       = new("driver", 1, intf_inst, ,atmc_gen2src_chan); 
	ATMC_GEN_END
	SCN_GEN_START
   driver       = new("driver", 1, intf_inst, ,scen_gen2src_chan); 
	SCN_GEN_END
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
	ATMC_GEN_START
   driver       = new("driver", 1, ,atmc_gen2src_chan); 
	ATMC_GEN_END
	SCN_GEN_START
   driver       = new("driver", 1, ,scen_gen2src_chan); 
	SCN_GEN_END
   FULL_DUPLEX_FNC_BFM_END
   monitor      = new("monitor", 1, intf_inst, ,mon_chan); 
   SING_DRV_END
   MULT_DRV_START
   // ToDo : Add/Remove appropriate argument in new() when multiple drivers are used. instances are created with
   //respect to first driver selected 
   FULL_DUPLEX_PHY_BFM_START
   driver_RPTNO     = new("driver_RPTNO", RPTNO, intf_inst[RPTNO]);   //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
   driver_RPTNO     = new("driver_RPTNO", RPTNO);   //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_FNC_BFM_END
   monitor      = new("monitor", 1, intf_inst[0], ,mon_chan); 
   // ToDo : Add required instance of driver/monitor 
   MULT_DRV_END
   FD_DRIV_END
   GNRC_DRIV_START
   SING_DRV_START
   FULL_DUPLEX_PHY_BFM_START
   driver       = new("driver", 1, intf_inst);
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
   driver       = new("driver", 1);
   FULL_DUPLEX_FNC_BFM_END
   monitor      = new("monitor", 1, intf_inst, ,mon_chan); 
   SING_DRV_END
   MULT_DRV_START
   //ToDo : Call new for other drivers if multiple drivers are used
   FULL_DUPLEX_PHY_BFM_START
   driver_RPTNO     = new("driver_RPTNO", RPTNO, intf_inst[RPTNO]);  //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
   driver_RPTNO     = new("driver_RPTNO", RPTNO);  //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_FNC_BFM_END
   monitor      = new("monitor", 1, intf_inst[0]); 
   // ToDo : Add required instance of driver/monitor 
   MULT_DRV_END
   GNRC_DRIV_END  
   cov      = new;
   mon2cov  = new(cov);
   monitor.append_callback(mon2cov);
   ATMC_GEN_START 
   atmc_gen.stop_after_n_insts = cfg.num_trans;
   ATMC_GEN_END
   SCN_GEN_START
   scen_gen.stop_after_n_insts = cfg.num_trans;
   scen_gen.stop_after_n_scenarios= cfg.num_scen;
   SCN_GEN_END
   MS_GEN_START
   gen_ms.stop_after_n_insts = cfg.num_trans;
   gen_ms.stop_after_n_scenarios= cfg.num_scen;
   MS_GEN_END 
   PERF_START
   
   this.monitor_perf_db = new("Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   monitor_perf_an = new("perf_an",this.monitor_perf_db, , , );
   monitor_perf_cb = new(monitor_perf_an);
   
   this.driver_perf_db = new("Driver Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   driver_perf_an = new("driver_perf_an",this.driver_perf_db,,);
   SING_DRV_START
   driver_perf_cb = new(driver_perf_an);
   SING_DRV_END
   MULT_DRV_START
   driver_perf_cb_RPTNO = new(driver_perf_an);   //VMMGEN_RPT_ON_XACT
   MULT_DRV_END

   begin
      TR  pkt = new();
      // ToDo: Add the shceme in create_table for monitor 
      vmm_sql_table monitor_perf_tbl = monitor_perf_db.create_table("TR", "");

      // ToDo: Insert the data string as per given scheme in create_table() instead of null string
      monitor_perf_tbl.insert("");
      monitor_perf_db.commit();
      //DISABLE PERFORMANCE-ANALYZER :Comment the following line to avoid the performance analyzer in monitor 
      monitor.append_callback(monitor_perf_cb);
   end

   begin
      // ToDo: Add the scheme in create_table for driver
      // ToDo: Add table for other drivers, in case of multiple drivers
      vmm_sql_table driver_perf_tbl = driver_perf_db.create_table("XACT", "");

      // ToDo: Insert the data string as per given scheme in create_table() instead of null string
      driver_perf_tbl.insert("");
      driver_perf_db.commit();
      SING_DRV_START
      //DISABLE PERFORMANCE-ANALYZER :Comment the following line to avoid the performance analyzer in driver 
      driver.append_callback(driver_perf_cb);
      SING_DRV_END
      MULT_DRV_START
      //DISABLE PERFORMANCE-ANALYZER :Comment the following lines to avoid the performance analyzer in drivers 
      driver_RPTNO.append_callback(driver_perf_cb_RPTNO);           //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
   end
   PERF_END
   SCBD_EN_START
   sb = new("SCBD");
   bfm_sb_cb = new(sb);  //Instantiating the driver callback
   SING_DRV_START 
   driver.append_callback(bfm_sb_cb); //Appending the callback with driver
   SING_DRV_END
   MULT_DRV_START
   driver_0.append_callback(bfm_sb_cb);  
   MULT_DRV_END
   SCBD_EN_END
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
   this.monitor.notify.register_vmm_sb_ds(MON::OBSERVED, this.sb,
                                          vmm_sb_ds::EXPECT,
                                          vmm_sb_ds::IN_ORDER);
   SCB_INT_MTHD_SIX_END
   MULT_DRV_START
   MS_GEN_START
   //Connecting each driver's channel of its MS-generator channel
   this.TR_chan_RPTNO = driver_RPTNO.in_chan; //VMMGEN_RPT_ON_TR 
   MS_GEN_END
   ATMC_GEN_START
   //ToDo: Connect the required driver's channel with generator's channel 
   ATMC_GEN_END
   SCN_GEN_START
   //ToDo: Connect the required driver's channel with generator's channel 
   SCN_GEN_END 
   MULT_DRV_END
   `vmm_note(this.log, this.cfg.psdisplay());
   RAL_START
   MULT_DM_START
   SING_DRV_START
   this.DN1_host = new("RAL DN1 BFM","DN1_host",0,driver);
   SING_DRV_END
   MULT_DRV_START
   this.DN1_host = new("RAL DN1 BFM","DN2_host",0,driver_0);
   MULT_DRV_END
   super.ral.add_xactor(this.DN1_host);  //ToDo: User need to pass the domain name in second argument.
   //ToDo: User need to instantiate the other RAL BFMs and add them in the RAL access instance
   //e.g.
   //this.DN2_host = new("RAL DN2 BFM",0,<instance of other physical driver>);
   //super.ral.add_xactor(this.DN2_host,<Domain Name>);
   MULT_DM_END
   SING_DM_START
   SING_DRV_START
   this.host = new("RAL BFM","host",0,driver);
   SING_DRV_END
   MULT_DRV_START
   this.host = new("RAL BFM","host",0,driver_0);
   MULT_DRV_END 
   super.ral.add_xactor(this.host);
   SING_DM_END
   RAL_END
   // ToDo: Instantiate transactors, using XMRs to access interface instances

   // ToDo: Start transactors needed to configure the DUT

endfunction: build


task ENV::reset_dut();
   super.reset_dut();

   // ToDo: Apply hardware reset to DUT
endtask: reset_dut
RAL_START


task ENV::hw_reset();

   // ToDo: Apply hardware reset to DUT
endtask: hw_reset
RAL_END

   
task ENV::cfg_dut();
   super.cfg_dut();

   // ToDo: Configure DUT
endtask: cfg_dut
NORMAL_START


task ENV::start();
   super.start();
   MS_GEN_START
   gen_ms.start_xactor();
   MS_GEN_END
   ATMC_GEN_START
   atmc_gen.start_xactor();
   ATMC_GEN_END
   SCN_GEN_START
   scen_gen.start_xactor();
   SCN_GEN_END
   SING_DRV_START
   driver.start_xactor();
   monitor.start_xactor();
   SING_DRV_END
   MULT_DRV_START
   begin `foreach_vmm_xactor(XACT, "/./", "/./") xact.start_xactor(); end  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   ATMC_GEN_START
   this.end_vote.register_notification(this.atmc_gen.notify,TR_atomic_gen::DONE);
   ATMC_GEN_END
   SCN_GEN_START
   this.end_vote.register_notification(this.scen_gen.notify,TR_scenario_gen::DONE);
   SCN_GEN_END
   ATMC_GEN_START
   this.end_vote.register_channel(this.atmc_gen2src_chan);
   ATMC_GEN_END
   SCN_GEN_START
   this.end_vote.register_channel(this.scen_gen2src_chan);
   SCN_GEN_END
   this.end_vote.register_channel(this.mon_chan);
   SING_DRV_START
   this.end_vote.register_xactor(this.driver);
   SING_DRV_END
   MULT_DRV_START
   this.end_vote.register_xactor(this.driver_RPTNO);       //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
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

  // ToDo: Start all transactors
endtask: start


task ENV::stop();
   super.stop();

   // ToDo: Stop all generators
   ATMC_GEN_START 
   atmc_gen.stop_xactor();
   ATMC_GEN_END
   SCN_GEN_START  
   scen_gen.stop_xactor();
   SCN_GEN_END
   MS_GEN_START 
   gen_ms.stop_xactor();
   MS_GEN_END
   SING_DRV_START
   driver.stop_xactor();
   monitor.stop_xactor();
   SING_DRV_END
   MULT_DRV_START
   begin `foreach_vmm_xactor(XACT, "/./", "/./") xact.stop_xactor(); end  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
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
   
endtask: do_start
SCB_INT_MTHD_THREE_END
SCB_INT_MTHD_FOUR_START


task ENV::do_start();

   fork
      forever begin

      // ToDo: OBSERVED enum should exist in monitor class
         this.monitor.notify.wait_for(MON::OBSERVED); 
         this.sb.expect_in_order(
         this.monitor.notify.status(MON::OBSERVED));
      end
   join_none
   
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
   this.monitor_perf_an.save_db();
   this.monitor_perf_an.report();
   this.driver_perf_an.save_db();
   this.driver_perf_an.report();
   PERF_END
   SCBD_EN_START 
   sb.report();
   SCBD_EN_END
   // ToDo: Generate the Final Report

endtask: report

`endif // ENV__SV
