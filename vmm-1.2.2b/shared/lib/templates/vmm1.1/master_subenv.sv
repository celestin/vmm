//
// Template for VMM-compliant Sub-Environment
// <MASTER_SE> Name of Sub-environmnet class

`ifndef MASTER_SE__SV
`define MASTER_SE__SV

SCB_INT_MTHD_FIVE_START

class sb_notify_cb extends vmm_notify_callbacks;
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
class MASTER_SE_cfg;

   // ToDo: Add properties for configuring MASTER_SE

endclass: MASTER_SE_cfg


class MASTER_SE extends vmm_subenv;

   // VNAME Virtual Interface Instance
   SING_DRV_START
   virtual IF intf_inst;
   SING_DRV_END
   MULT_DRV_START
   virtual IF intf_inst[INTF_COUNT];
   MULT_DRV_END
   // VNAME configuration Instance 
   CFG cfg;

   ATMC_GEN_START
   TR_channel    atmc_gen2src_chan;
   TR_atomic_gen atmc_gen;
   ATMC_GEN_END
   SCN_GEN_START 
   TR_channel      scen_gen2src_chan;
   TR_scenario_gen scen_gen;
   SCN_GEN_END
   TR_channel mon_chan;
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

   // VNAME Sunenv configuration Instance 
   protected MASTER_SE_cfg mst_cfg;  
   local MASTER_SE_cfg reset_cfg;

   SING_DRV_START
   XACT driver;  
   SING_DRV_END
   MULT_DRV_START
   //Multiple driver instantiation
   XACT driver_RPTNO;                      //VMMGEN_RPT_ON_XACT
   //ToDo: Instantiate other drivers here. 
   MULT_DRV_END
   MON monitor;
   SCBD_EN_START
   SB sb;
   SCBD_EN_END
   COV cov;
   
   // VMM Consensus handle
   vmm_consensus end_vote;

   // Add Callbacks
   MON_2cov_connect mon2cov;
   SCBD_EN_START
   XACT_sb_callbacks bfm_sb_cb;
   SCBD_EN_END
   SCB_INT_MTHD_ONE_START
   MON_sb_cb  mon_sb_cb;
   SCB_INT_MTHD_ONE_END

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
     
   // ToDo: add sub environmnet properties here

   MACRO_START
   // VMM shorthand macro which provides default implementation for
   // start/stop/reset xactor methods
   `vmm_subenv_member_begin(MASTER_SE)
      ATMC_GEN_START
      `vmm_subenv_member_xactor(atmc_gen, DO_ALL)
      `vmm_subenv_member_channel(atmc_gen2src_chan, DO_ALL)
      ATMC_GEN_END  
      SCN_GEN_START 
      `vmm_subenv_member_xactor(scen_gen, DO_ALL)
      `vmm_subenv_member_channel(scen_gen2src_chan, DO_ALL)
      SCN_GEN_END
      MS_GEN_START
      `vmm_subenv_member_xactor(gen_ms, DO_ALL)
      MS_GEN_END 
      `vmm_subenv_member_channel(mon_chan, DO_ALL)
      SING_DRV_START
      `vmm_env_member_xactor(driver, DO_ALL)
      SING_DRV_END
      MULT_DRV_START
      `vmm_env_member_xactor(driver_RPTNO, DO_ALL)  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
      `vmm_subenv_member_xactor(monitor, DO_ALL)
      `vmm_subenv_member_vmm_data(cfg, DO_ALL)
      // ToDo: add properties using macros here

   `vmm_subenv_member_end(MASTER_SE)
   MACRO_END

   extern function new(string name = "",
                       string inst = "",
                       vmm_consensus end_vote,
                       CFG cfg,
                       SING_DRV_START
                       virtual IF intf_inst,
                       SING_DRV_END
                       MULT_DRV_START
                       virtual IF intf_inst[INTF_COUNT],
                       MULT_DRV_END
                       MASTER_SE_cfg mst_cfg = null);

   // VMM Sub Environment Steps                    
   extern virtual task config_se();
   extern function build(); 
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   extern virtual task cleanup();
   extern virtual function void report();
   MACRO_START
   SCB_INT_MTHD_THREE_START
   extern virtual task do_start();
   SCB_INT_MTHD_THREE_END
   SCB_INT_MTHD_FOUR_START
   extern virtual task do_start();
   SCB_INT_MTHD_FOUR_END
   MACRO_END
endclass: MASTER_SE


function MASTER_SE::new (string name, string inst,
                         vmm_consensus end_vote, 
                         CFG cfg, 
                         SING_DRV_START
                         virtual IF intf_inst,
                         SING_DRV_END
                         MULT_DRV_START
                         virtual IF intf_inst[INTF_COUNT],
                         MULT_DRV_END
                         MASTER_SE_cfg mst_cfg = null);
   super.new(name,inst,end_vote);
   if(mst_cfg == null) mst_cfg=new();  
   this.mst_cfg = mst_cfg;
   this.reset_cfg = mst_cfg;
   this.end_vote  = end_vote;
   // Save a copy of the configuration class
   this.cfg = cfg;
   // Save a copy of the interface passed by env
   this.intf_inst = intf_inst;

endfunction: new

function MASTER_SE::build();   
   // ToDo : Edit required constuctor argument here.
   MS_GEN_START
   gen_ms = new("Multistream Scenario Gen", 2);
   ms_scn = new();
   SING_DRV_START
   TR_chan = new("TR channel_c","channel");                     //VMMGEN_RPT_ON_TR
   gen_ms.register_channel("TR_scenario_channel", TR_chan);     //VMMGEN_RPT_ON_TR
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR channel_cRPTNO","channel_RPTNO");    //VMMGEN_RPT_ON_TR
   gen_ms.register_channel("TR_scenario_channel_RPTNO", TR_chan_RPTNO);     //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   //ToDo: Instantiate other required channels of required transaction types and register them 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   //ToDo: Register required scenarios
   MS_GEN_END
   mon_chan     = new("Mon_Chan", "mon_chan");
   ATMC_GEN_START
   atmc_gen2src_chan = new("Gen_To_Drvr_Chan", "atmc_gen2src_chan");
   atmc_gen          = new("atmc_gen", 1, atmc_gen2src_chan);
   ATMC_GEN_END
   SCN_GEN_START 
   scen_gen2src_chan = new("Gen_To_Drvr_Chan", "scen_gen2src_chan");
   scen_gen          = new("scen_gen", 1, scen_gen2src_chan);
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
   driver_RPTNO = new("driver_RPTNO", RPTNO, intf_inst[RPTNO]);            //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
   driver_RPTNO = new("driver_RPTNO", RPTNO);            //VMMGEN_RPT_ON_XACT
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
   // ToDo : Add/Remove appropriate argument in new() when multiple drivers are used. instances are created with
   //respect to first driver selected 
   FULL_DUPLEX_PHY_BFM_START
   driver_RPTNO = new("driver_RPTNO", RPTNO, intf_inst[RPTNO]);            //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_PHY_BFM_END
   FULL_DUPLEX_FNC_BFM_START
   driver_RPTNO = new("driver_RPTNO", RPTNO);            //VMMGEN_RPT_ON_XACT
   FULL_DUPLEX_FNC_BFM_END
   monitor      = new("monitor", 1, intf_inst[0]);
   // ToDo : Add required instance of driver/monitor
   MULT_DRV_END
   GNRC_DRIV_END  
   cov          = new;
   mon2cov      = new(cov);
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
      monitor.append_callback(monitor_perf_cb);
   end

   begin
      // ToDo: Add the shceme in create_table for driver
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
      driver_RPTNO.append_callback(driver_perf_cb_RPTNO);  //VMMGEN_RPT_ON_XACT
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
                                          vmm_sb_ds::EXPECT, vmm_sb_ds::IN_ORDER);
   SCB_INT_MTHD_SIX_END
   `vmm_note(this.log, this.cfg.psdisplay());
   MULT_DRV_START
   MS_GEN_START
   //Connecting each driver's channel of its MS-generator channel
   this.TR_chan_RPTNO = driver_RPTNO.in_chan; //VMMGEN_RPT_ON_TR 
   MS_GEN_END
   MULT_DRV_END

   // Enable Coverage
   monitor.prepend_callback(mon2cov);

   // ToDo: Instantiate transactors, using XMRs to access interface instances

endfunction: build


task MASTER_SE::config_se();
   // ToDo: Configure sub env and portion of associated DUT if any

   super.configured();
   if(this.cfg != null) begin
     `vmm_note(log, "configured() executed");
   end

endtask : config_se
NORMAL_START


task MASTER_SE::start();
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

  // ToDo: Start all transactors in MASTER_SE
endtask: start


task MASTER_SE::stop();
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


task MASTER_SE::do_start();
   super.start();
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


task MASTER_SE::do_start();

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


task MASTER_SE::cleanup();
   super.cleanup();
   
   // ToDo: Verify end-of-test conditions
endtask: cleanup


function void MASTER_SE::report();
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
   // ToDo: Report status or coverage information
endfunction: report

`endif // MASTER_SE__SV
