//
// Template for VMM-compliant verification environment
// <ENV>       Name of Environment class
// <CFG>       Name of the configuration class
// <TR>        Name of the transaction descriptor
// <XACT>      Name of the master driver
// <REC>       Name of the slave receiver 
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

   `vmm_typename(sb_notify_cb)
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
COMMON_START
TST_EXPL_START

class ENV extends vmm_env;
TST_EXPL_END
TST_IMPL_START

class ENV extends vmm_group;
TST_IMPL_END
COMMON_END
RAL_START
TST_EXPL_START

class ENV extends vmm_ral_env;
TST_EXPL_END
TST_IMPL_START

class ENV extends vmm_group;
TST_IMPL_END
RAL_END

   `vmm_typename(ENV)
   vmm_version vmm_ver;
   CFG cfg;
   SCBD_EN_START 
   SB sb;
   SCBD_EN_END
   RAL_START
   ral_block_VNAME ral_model;
   TST_IMPL_START
   vmm_ral_access  ral;
   TST_IMPL_END
   MULT_DM_START
   XACT_DN1_ral DN1_host;
   XACT_DN2_ral DN2_host;
   //ToDo : Instantiate other RAL BFMs, if more than two domains are used.
   
   MULT_DM_END
   SING_DM_START
   XACT_ral host;
   SING_DM_END
   RAL_END
   MNTR_OBS_MTHD_ONE_START 
   TR_channel mon_chan;
   MNTR_OBS_MTHD_ONE_END
   ATMC_GEN_START
   TR_atomic_gen atmc_gen;
   ATMC_GEN_END
   SCN_GEN_START
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
   GEN_SL_RCVR_START
   REC receiver;
   TR_channel rcvr_chan;
   GEN_SL_RCVR_END
   MON monitor;   
   COV cov;
   MNTR_OBS_MTHD_ONE_START 
   MON_2cov_connect mon2cov;
   MNTR_OBS_MTHD_ONE_END
   MNTR_OBS_MTHD_TWO_START 
   MNTR_OBS_MTHD_TWO_Q_START
   MON_2cov_connect mon2cov;
   MNTR_OBS_MTHD_TWO_Q_END
   MNTR_OBS_MTHD_TWO_END
   SCBD_EN_START
   XACT_sb_cb bfm_sb_cb;
   SCBD_EN_END
   PERF_START
   MON_perf_cb       monitor_perf_cb;
   vmm_sql_db_ascii  monitor_perf_db;
   vmm_perf_analyzer monitor_perf_an;
   vmm_sql_db_ascii  driver_perf_db;
   vmm_perf_analyzer driver_perf_an;
   SING_DRV_START
   XACT_perf_cb driver_perf_cb;
   SING_DRV_END
   MULT_DRV_START
   XACT_perf_cb driver_perf_cb_RPTNO;   //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   PERF_END
   SCB_INT_MTHD_ONE_START
   MON_sb_cb mon_sb_cb;
   SCB_INT_MTHD_ONE_END
   MNTR_OBS_MTHD_FOUR_START
   SCBD_EN_START
   SB_notify_observer#(TR) sb_observe_start;
   SCBD_EN_END
   COV_notify_observer#(TR) cov_observe_start;
   MNTR_OBS_MTHD_FOUR_END
   MNTR_OBS_MTHD_THREE_START
   MON_to_subscribers_cb mon_2_subs_cb;
   MNTR_OBS_MTHD_THREE_END
   TST_EXPL_START
     XCT_IMPL_START
   vmm_timeline    env_tml; //Instance of timeline to co-ordinate all the phases of components
     XCT_IMPL_END
   TST_EXPL_END
   RTLCFG_START
   env_config  env_cfg;
   RTLCFG_END 

   MACRO_START
   TST_EXPL_START
   `vmm_env_member_begin(ENV)
      // ToDo: Add required vmm env member

      RAL_START
      MULT_DM_START
      `vmm_env_member_xactor(DN1_host, DO_ALL)
      `vmm_env_member_xactor(DN2_host, DO_ALL)
      MULT_DM_END
      SING_DM_START
      `vmm_env_member_xactor(host, DO_ALL)
      SING_DM_END
      RAL_END 
      ATMC_GEN_START 
      `vmm_env_member_xactor(atmc_gen, DO_ALL)
      ATMC_GEN_END
      SCN_GEN_START
      `vmm_env_member_xactor(scen_gen, DO_ALL)
      SCN_GEN_END 
      SING_DRV_START 
      `vmm_env_member_xactor(driver, DO_ALL)
      SING_DRV_END
      MULT_DRV_START
      `vmm_env_member_xactor(driver_RPTNO, DO_ALL)  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
       GEN_SL_RCVR_START
      `vmm_env_member_xactor(receiver, DO_ALL)
       GEN_SL_RCVR_END
      `vmm_env_member_xactor(monitor, DO_ALL)
       MNTR_OBS_MTHD_ONE_START
      `vmm_env_member_channel(mon_chan, DO_ALL)
       MNTR_OBS_MTHD_ONE_END
       MS_GEN_START
      `vmm_env_member_xactor(gen_ms, DO_ALL)
       MS_GEN_END
   `vmm_env_member_end(ENV)
   TST_EXPL_END
   TST_IMPL_START
   TST_IMPL_END
   MACRO_END
   TST_IMPL_START
   
   extern function new(string name, vmm_group parent=null);
   extern virtual function void build_ph();
   extern virtual function void configure_ph();
   extern virtual function void connect_ph();
   extern function void start_of_sim_ph();
   extern virtual task reset_ph();
   extern virtual task config_dut_ph();
   extern virtual task start_ph();
   extern virtual task run_ph();
   extern virtual task shutdown_ph();
   extern virtual task cleanup_ph();
   extern virtual function void report_ph();
   TST_IMPL_END
   TST_EXPL_START
   
   extern function new(string name);
   extern virtual function void build();
   extern virtual function void gen_cfg();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   extern virtual function void connect_children();
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   MACRO_START
   extern virtual task do_start();
   extern virtual task do_stop();
   MACRO_END
   extern virtual task wait_for_end();
   extern virtual task cleanup();
   extern virtual task report();
   TST_EXPL_END
   RAL_START
   extern virtual task hw_reset();
   RAL_END
   extern virtual task automatic start_record_replay(vmm_channel chan, int i);

endclass: ENV
TST_EXPL_START


function ENV::new(string name);
   super.new(name);
   NORMAL_START
   cfg = new ("CFG", this);
   NORMAL_END
   MACRO_START
   cfg = new();
   MACRO_END
TST_EXPL_END
TST_IMPL_START


function ENV::new(string name, vmm_group parent=null);
   super.new(name,"env",parent);
TST_IMPL_END
   vmm_ver = new();
   vmm_ver.display("**** Note : ");
   $timeformat(-9, 0, "ns", 1);
endfunction: new
TST_EXPL_START


function void ENV::build();
   super.build();
   XCT_IMPL_START 
   env_tml = new("timeline","env_tml",this);
   XCT_IMPL_END
   MS_GEN_START
   XCT_IMPL_START
   gen_ms = new("Multistream Scenario Gen", 0, env_tml);
   XCT_IMPL_END
   XCT_EXPL_START
   gen_ms = new("Multistream Scenario Gen", 0,this);
   XCT_EXPL_END
   SING_DRV_START
   TR_chan = new("TR_channel_c","channel");  
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR_channel_cRPTNO","channel_RPTNO");  //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   SING_DRV_START
   gen_ms.register_channel("TR_scenario_channel", TR_chan); 
   SING_DRV_END
   MULT_DRV_START
   gen_ms.register_channel("TR_scenario_channel_RPTNO", TR_chan_RPTNO); //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   ms_scn = VNAME_ms_scen::create_instance(this,"ms_scn"); 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   //ToDo: Register required scenarios
   MS_GEN_END
   ATMC_GEN_START
   XCT_IMPL_START 
   atmc_gen = new("atmc_gen", 1, ,env_tml);
   XCT_IMPL_END 
   XCT_EXPL_START
   atmc_gen = new("atmc_gen", 1,,this); 
   XCT_EXPL_END 
   ATMC_GEN_END
   SCN_GEN_START
   XCT_IMPL_START 
   scen_gen = new("scen_gen", 1, ,env_tml);
   XCT_IMPL_END 
   XCT_EXPL_START
   scen_gen = new("scen_gen", 1,,this); 
   XCT_EXPL_END 
   SCN_GEN_END
   ATMC_GEN_START
   atmc_gen.stop_after_n_insts = cfg.num_trans;
   ATMC_GEN_END
   SCN_GEN_START
   scen_gen.stop_after_n_insts = cfg.num_trans;
   scen_gen.stop_after_n_scenarios = cfg.num_scen;
   SCN_GEN_END
   MS_GEN_START
   gen_ms.stop_after_n_insts = cfg.num_trans;
   gen_ms.stop_after_n_scenarios = cfg.num_scen;
   MS_GEN_END
   FD_DRIV_START    
   // ToDo : Add appropriate argument in new()
   DRIV_CHNL_START
   XCT_IMPL_START
   SING_DRV_START 
	ATMC_GEN_START
   driver = new("Driver","drv", 1, env_tml, ,atmc_gen.out_chan); 
	ATMC_GEN_END
	SCN_GEN_START
   driver = new("Driver","drv", 1, env_tml, ,scen_gen.out_chan);
	SCN_GEN_END
   SING_DRV_END
   MULT_DRV_START
   // ToDo : User need to connect the channel
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, env_tml);  //VMMGEN_RPT_ON_XACT 
   MULT_DRV_END
   XCT_IMPL_END
   XCT_EXPL_START
   SING_DRV_START 
	ATMC_GEN_START
   driver = new("Driver","drv", 1,this, ,atmc_gen.out_chan);
	ATMC_GEN_END
	SCN_GEN_START
   driver = new("Driver","drv", 1,this, ,scen_gen.out_chan);
	SCN_GEN_END
   SING_DRV_END
   MULT_DRV_START
   // ToDo : User need to connect the channel
 
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO",RPTNO,this);     //VMMGEN_RPT_ON_XACT 
   MULT_DRV_END 
   XCT_EXPL_END
   DRIV_CHNL_END
   DRIV_GEN_TLM_START
   XCT_IMPL_START
   SING_DRV_START
   driver = new("Driver","drv", 1, env_tml); 
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, env_tml);          //VMMGEN_RPT_ON_XACT 
   MULT_DRV_END
   XCT_IMPL_END
   XCT_EXPL_START
   SING_DRV_START
   driver = new("Driver","drv", 1,this); 
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO,this);  //VMMGEN_RPT_ON_XACT  
   MULT_DRV_END
   XCT_EXPL_END 
   DRIV_GEN_TLM_END
   FD_DRIV_END
   GNRC_DRIV_START 
   XCT_IMPL_START
   SING_DRV_START
   driver = new("Driver","drv", 1, env_tml); 
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, env_tml); //VMMGEN_RPT_ON_XACT 
   MULT_DRV_END
   XCT_IMPL_END
   XCT_EXPL_START
   SING_DRV_START
   driver = new("Driver","drv", 1,this); 
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO,this);  //VMMGEN_RPT_ON_XACT  
   MULT_DRV_END
   XCT_EXPL_END
   GNRC_DRIV_END 
   GEN_SL_RCVR_START
   rcvr_chan = new("RCVR_CHANNEL", "");
   XCT_IMPL_START
   receiver  = new("SLAVE RECEIVER","rec", 1, rcvr_chan,env_tml); 
   XCT_IMPL_END
   XCT_EXPL_START
   receiver  = new("SLAVE RECEIVER","rec", 1, rcvr_chan,this); 
   XCT_EXPL_END
   GEN_SL_RCVR_END 
   MNTR_OBS_MTHD_ONE_START 
   mon_chan = new("Mon_TR_channel_c", "mon_chan");
   XCT_IMPL_START
   monitor = new("Monitor","mon", 1, env_tml, ,mon_chan); 
   XCT_IMPL_END 
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this, ,mon_chan); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_ONE_END
      MNTR_OBS_MTHD_TWO_START
   XCT_IMPL_START 
   monitor = new("Monitor","mon", 1, env_tml); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START
   XCT_IMPL_START 
   monitor = new("Monitor","mon", 1, env_tml); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START
   XCT_IMPL_START 
   monitor = new("Monitor","mon", 1, env_tml); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_FOUR_END
TST_EXPL_END
TST_IMPL_START


function void ENV::build_ph();
   super.build_ph();
   MS_GEN_START
   gen_ms = new("Multistream Scenario Gen", 0,this);
   SING_DRV_START
   TR_chan = new("TR_channel_c","channel");  
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR_channel_cRPTNO","channel_RPTNO");  //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   SING_DRV_START
   gen_ms.register_channel("TR_scenario_channel", TR_chan); 
   SING_DRV_END
   MULT_DRV_START
   gen_ms.register_channel("TR_scenario_channel_RPTNO", TR_chan_RPTNO); //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   //ToDo : Instantiate other required channels of required transaction types and register them
   MS_GEN_END
   ATMC_GEN_START
   atmc_gen = new("atmc_gen", 1,,this); 
   ATMC_GEN_END
   SCN_GEN_START
   scen_gen = new("atmc_gen", 1,,this); 
   SCN_GEN_END 
   // ToDo : Add appropriate argument in new() 
  
   FD_DRIV_START 
   DRIV_CHNL_START
   SING_DRV_START
	ATMC_GEN_START
   driver = new("Driver","drv", 1, this, ,atmc_gen.out_chan); 
	ATMC_GEN_END
	SCN_GEN_START
   driver = new("Driver","drv", 1, this, ,scen_gen.out_chan); 
	SCN_GEN_END
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, this);  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   DRIV_CHNL_END
   DRIV_GEN_TLM_START
   SING_DRV_START
   driver = new("Driver","drv", 1, this);
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, this);  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END 
   DRIV_GEN_TLM_END
   FD_DRIV_END
   GNRC_DRIV_START 
   SING_DRV_START
   driver = new("Driver","drv", 1, this);  
   SING_DRV_END
   MULT_DRV_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, this);  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   GNRC_DRIV_END 
   GEN_SL_RCVR_START
   rcvr_chan = new("RCVR_CHANNEL", "");
   receiver  = new("SLAVE RECEIVER","rec", 1, rcvr_chan,this); 
   GEN_SL_RCVR_END 
   MNTR_OBS_MTHD_ONE_START 
   mon_chan = new("Mon_TR_channel_c", "mon_chan");
   monitor = new("Monitor","mon", 1, this, ,mon_chan); 
   MNTR_OBS_MTHD_ONE_END
   MNTR_OBS_MTHD_TWO_START
   monitor = new("Monitor","mon", 1, this); 
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START
   monitor = new("Monitor","mon", 1, this); 
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START
   monitor = new("Monitor","mon", 1, this); 
   MNTR_OBS_MTHD_FOUR_END
   TST_IMPL_END
   RTLCFG_START
   env_cfg.map_to_name("^");
   SING_DRV_START
   env_cfg.mst_cfg.map_to_name("env:drv");
   SING_DRV_END
   MULT_DRV_START
   env_cfg.mst_cfg_RPTNO.map_to_name("env:drv_RPTNO");  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   GEN_SL_RCVR_START
   env_cfg.slv_cfg.map_to_name("env:rec");
   GEN_SL_RCVR_END
   //ToDo : Add the mapping if any other RTL config objects are defined.
   
   RTLCFG_END
   TST_IMPL_START
   //ToDo: Register other components,channels and notifications if added by user  
  
   ATMC_GEN_START 
   vote.register_xactor(atmc_gen);
   ATMC_GEN_END  
   SCN_GEN_START
   vote.register_xactor(scen_gen);
   SCN_GEN_END
   SING_DRV_START
   vote.register_xactor(driver);
   SING_DRV_END
   MULT_DRV_START
   vote.register_xactor(driver_RPTNO);  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   TST_IMPL_END
   cov = new(); //Instantiating the coverage class
   MNTR_OBS_MTHD_ONE_START
   mon2cov  = new(cov);
   monitor.append_callback(mon2cov);
   MNTR_OBS_MTHD_ONE_END
   MNTR_OBS_MTHD_TWO_START
   MNTR_OBS_MTHD_TWO_Q_START
   mon2cov  = new(cov);
   monitor.append_callback(mon2cov);
   MNTR_OBS_MTHD_TWO_Q_END
   MNTR_OBS_MTHD_TWO_END
   PERF_START
   this.monitor_perf_db = new("Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   
   monitor_perf_an = new("perf_an",this.monitor_perf_db, , , );
   monitor_perf_cb = new(monitor_perf_an);
   this.monitor_perf_db = new("Monitor Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   this.driver_perf_db  = new("Driver Perfomance Database");
   // ToDo: Add required data in the new (ex: max no of initiators etc.)
   
   driver_perf_an = new("driver_perf_an",this.driver_perf_db,,);
   SING_DRV_START
   driver_perf_cb = new(driver_perf_an);
   SING_DRV_END
   MULT_DRV_START
   driver_perf_cb_RPTNO = new(driver_perf_an);   //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   begin
      TR pkt = new();
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
      driver_RPTNO.append_callback(driver_perf_cb_RPTNO);  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
   end
   PERF_END
   SCBD_EN_START
   sb = new("SCBD(GEN-MON)");
   bfm_sb_cb = new();              //Instance of Generator-Scoreboard callback
   //Appending the callback with driver
   SING_DRV_START
   driver.append_callback(bfm_sb_cb); //VMMGEN_RPT_ON_XACT 
   SING_DRV_END
   MULT_DRV_START
   driver_0.append_callback(bfm_sb_cb); 
   MULT_DRV_END
   SCBD_EN_END 
   MNTR_OBS_MTHD_FOUR_START
   SCBD_EN_START
   sb_observe_start = new (sb, monitor.notify, monitor.TRANS_START);
   SCBD_EN_END
   cov_observe_start = new (cov, monitor.notify, monitor.TRANS_START);
   MNTR_OBS_MTHD_FOUR_END
   MNTR_OBS_MTHD_THREE_START
   mon_2_subs_cb = new();
   this.monitor.notify.append_callback(monitor.TRANS_START, mon_2_subs_cb);
   MNTR_OBS_MTHD_THREE_END
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
   RAL_START
   this.ral_model = new();
   TST_IMPL_START
   this.ral = new(this, "ral");
   this.ral.set_model(this.ral_model);
   TST_IMPL_END
   TST_EXPL_START
   super.ral.set_model(this.ral_model);
   TST_EXPL_END
   MULT_DM_START
   SING_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,driver);
   SING_DRV_END
   MULT_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,driver_0);
   MULT_DRV_END
   TST_IMPL_START
   this.ral.add_xactor(this.DN1_host);  //ToDo: User need to pass the domain name in second argument.
   TST_IMPL_END
   TST_EXPL_START
   super.ral.add_xactor(this.DN1_host);  //ToDo: User need to pass the domain name in second argument
   TST_EXPL_END
   //ToDo: User need to instantiate the other RAL BFMs and add them in the RAL access instance
   //e.g.
   //this.DN2_host = new("RAL DN2 BFM",0,<instance of other physical driver>);
   TST_IMPL_START
   //this.ral.add_xactor(this.DN2_host,"<Domain Name>");
   TST_IMPL_END
   TST_EXPL_START
   //super.ral.add_xactor(this.DN2_host,"<Domain Name>");
   TST_EXPL_END
   MULT_DM_END
   SING_DM_START
   SING_DRV_START
   this.host = new("RAL BFM","host",0,driver);
   SING_DRV_END
   MULT_DRV_START
   this.host = new("RAL BFM","host",0,driver_0);
   MULT_DRV_END
   TST_EXPL_START
   super.ral.add_xactor(this.host);
   TST_EXPL_END
   TST_IMPL_START
   this.ral.add_xactor(this.host);
   TST_IMPL_END 
   SING_DM_END
   // ToDo: Instantiate transactors, using XMRs to access interface instances
   // ToDo: Register any required callbacks

   RAL_END
TST_EXPL_START
endfunction: build
TST_EXPL_END
TST_IMPL_START
endfunction: build_ph
TST_IMPL_END
TST_EXPL_START


function void ENV::gen_cfg();
   super.gen_cfg();
   if(cfg.randomize())
   begin 
     `vmm_note(log,$psprintf("No. of transactions are",cfg.num_trans));
     cfg.display("ENV config");
   end
   else
   begin
    `vmm_fatal(log, "Randomization of env. config failed");
   end 
endfunction : gen_cfg
TST_EXPL_END
TST_IMPL_START


function void ENV::configure_ph();
   super.configure_ph();
endfunction: configure_ph
TST_IMPL_END
TST_IMPL_START


function void ENV::connect_ph();
   super.connect_ph();
 TST_IMPL_END
TST_EXPL_START


function void ENV::connect_children();
TST_EXPL_END
   FD_DRIV_START 
   SING_DRV_START
   DRIV_CHNL_START
   //Connecting the driver's input channel with generator's output channel
	ATMC_GEN_START
   this.atmc_gen.out_chan = driver.in_chan;
	ATMC_GEN_END
	SCN_GEN_START
   this.scen_gen.out_chan = driver.in_chan;
	SCN_GEN_END
   DRIV_CHNL_END
   DRIV_TLM_B_TRANS_EX_START 
	ATMC_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.atmc_gen.out_chan,driver.drv_b_export,vmm_tlm::TLM_BLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.scen_gen.out_chan,driver.drv_b_export,vmm_tlm::TLM_BLOCKING_PORT);
	SCN_GEN_END
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
	ATMC_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.atmc_gen.out_chan,driver.drv_nb_export,vmm_tlm::TLM_NONBLOCKING_FW_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.scen_gen.out_chan,driver.drv_nb_export,vmm_tlm::TLM_NONBLOCKING_FW_PORT);
	SCN_GEN_END
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_NB_TRANS_EX_START
	ATMC_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.atmc_gen.out_chan,driver.drv_nb_bidir,vmm_tlm::TLM_NONBLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.scen_gen.out_chan,driver.drv_nb_bidir,vmm_tlm::TLM_NONBLOCKING_PORT);
	SCN_GEN_END
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
	ATMC_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.atmc_gen.out_chan,driver.drv_target_exp,vmm_tlm::TLM_NONBLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(, , TR)::tlm_bind(this.scen_gen.out_chan,driver.drv_target_exp,vmm_tlm::TLM_NONBLOCKING_PORT);
	SCN_GEN_END
   DRIV_TLM_SMPL_TRGT_SCKT_END
   MS_GEN_START
   //Connecting each driver's channel of its MS-generator channel
   this.TR_chan = driver.in_chan; 
   MS_GEN_END
   SING_DRV_END
   FD_DRIV_END
   MULT_DRV_START
   MS_GEN_START
   this.TR_chan_RPTNO = driver_RPTNO.in_chan; //VMMGEN_RPT_ON_TR 
   MS_GEN_END
   ATMC_GEN_START
   //ToDo: Connect the required driver's channel with generator's channel 
   ATMC_GEN_END
   SCN_GEN_START
   //ToDo: Connect the required driver's channel with generator's channel 
   SCN_GEN_END 
   MULT_DRV_END
   MNTR_OBS_MTHD_TWO_START
   MNTR_OBS_MTHD_TWO_NQ_START
   //Connecting the monitor's analysis port with SB's expected analysis export.
   this.monitor.mon_analysis_port.tlm_bind(cov.cov_export);
   MNTR_OBS_MTHD_TWO_NQ_END
   SCBD_EN_START
   //Connecting the monitor's analysis port with coverage.
   this.monitor.mon_analysis_port.tlm_bind(sb.exp_ap);
   SCBD_EN_END
   MNTR_OBS_MTHD_TWO_END 
   SCBD_EN_START
   //Connecting the BFM callback's analysis port with SB's input analysis export.
   this.bfm_sb_cb.bfm_analysis_port.tlm_bind(sb.inp_ap);
   SCBD_EN_END
   MNTR_OBS_MTHD_THREE_START
   SCBD_EN_START
   this.mon_2_subs_cb.mon2sub_analys_port.tlm_bind(sb.exp_ap);
   SCBD_EN_END
   this.mon_2_subs_cb.mon2sub_analys_port.tlm_bind(cov.cov_export);
   MNTR_OBS_MTHD_THREE_END
TST_IMPL_START
  //Printing the complete hierarchy of env
  print_hierarchy();
endfunction: connect_ph
TST_IMPL_END
TST_EXPL_START
endfunction: connect_children
TST_EXPL_END
TST_IMPL_START


function void ENV::start_of_sim_ph();
   bit is_set; 
   super.start_of_sim_ph();
   //Env config
   $cast(this.cfg, vmm_opts::get_object_obj(is_set, this, "cfg"));
   if(!is_set) 
   begin
     `vmm_note(log, "no env config. passed, Using the default config");
      //If config. object is not passed through vmm_opts then instantiated cfg using factory which also could be overriden
      //using factory override methods
      cfg = CFG::create_instance(this,"cfg");
      cfg.randomize();
   end
   cfg.display("ENV config");
   //ToDo : functional configuration if needed 

   //Configuration is used in the start_of_sim_ph so that concatenated testcases could pass diff. config.
   ATMC_GEN_START
   atmc_gen.stop_after_n_insts = cfg.num_trans;
   ATMC_GEN_END
   SCN_GEN_START
   scen_gen.stop_after_n_insts = cfg.num_trans;
   scen_gen.stop_after_n_scenarios = cfg.num_scen;
   SCN_GEN_END
   MS_GEN_START
   gen_ms.stop_after_n_insts = cfg.num_trans;
   gen_ms.stop_after_n_scenarios = cfg.num_scen;
   MS_GEN_END
   //Enable the record/replay based on the mode selection
   ATMC_GEN_START
   if(cfg.mode != CFG::NORMAL) start_record_replay(atmc_gen.out_chan,1);
   ATMC_GEN_END
   SCN_GEN_START 
   if(cfg.mode != CFG::NORMAL) start_record_replay(scen_gen.out_chan,1);
   SCN_GEN_END
   MS_GEN_START 
	MULT_DRV_START
   if(cfg.mode != CFG::NORMAL) start_record_replay(TR_chan_RPTNO,RPTNO);  //VMMGEN_RPT_ON_TR 
	MULT_DRV_END
	SING_DRV_START
   if(cfg.mode != CFG::NORMAL) start_record_replay(TR_chan,1);
	SING_DRV_END
   MS_GEN_END
endfunction: start_of_sim_ph
TST_IMPL_END
TST_IMPL_START


task ENV::reset_ph();
   super.reset_ph();
   `vmm_note(log,"Resetting the DUT");
   //ToDo: Reset DUT

endtask: reset_ph
TST_IMPL_END
TST_EXPL_START


task ENV::reset_dut();
   super.reset_dut();
   RAL_START
   // ToDo: Apply hardware reset to DUT

   RAL_END
   XCT_IMPL_START
   env_tml.run_phase("build");
   env_tml.run_phase("configure");
   XCT_IMPL_END
   connect_children();
   XCT_IMPL_START
   env_tml.run_phase("connect");
   XCT_IMPL_END
   `vmm_note(log,"Resetting the DUT");
   //ToDo: Reset DUT
   
   XCT_IMPL_START 
   env_tml.run_phase("start_of_sim");
   env_tml.run_phase("reset");
   env_tml.run_phase("training");
   XCT_IMPL_END
endtask: reset_dut
TST_EXPL_END
RAL_START


task ENV::hw_reset();
   // ToDo: Apply hardware reset to DUT

endtask: hw_reset
RAL_END
TST_IMPL_START


task ENV::config_dut_ph();
   super.config_dut_ph();
   MS_GEN_START
   //ToDo: Configure the DUT
   ms_scn = VNAME_ms_scen::create_instance(this,"ms_scn"); 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   MS_GEN_END

endtask : config_dut_ph 
TST_IMPL_END
TST_EXPL_START


task ENV::cfg_dut();
   super.cfg_dut();
   XCT_IMPL_START
   env_tml.run_phase("config_dut");
   XCT_IMPL_END
   //ToDo: Configure the DUT

endtask : cfg_dut
TST_EXPL_END
TST_IMPL_START


task ENV::start_ph();
   super.start_ph();
  XCT_EXPL_START
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
   GEN_SL_RCVR_START
   receiver.start_xactor();
   GEN_SL_RCVR_END
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
   //ToDo: Start the other components if added later

   MULT_DRV_START
   begin `foreach_vmm_xactor(XACT, "/./", "/./")   xact.start_xactor(); end     //VMMGEN_RPT_ON_XACT   
   MULT_DRV_END
   XCT_EXPL_END
endtask: start_ph
TST_IMPL_END
TST_EXPL_START
NORMAL_START


task ENV::start();
   super.start();
NORMAL_END
MACRO_START


task ENV::do_start();
MACRO_END
   `vmm_note(log,"Starting all the transactors");
   XCT_IMPL_START
   env_tml.run_phase("start");
   env_tml.run_phase("start_of_test");
   env_tml.run_phase("run_test");
   XCT_IMPL_END
   XCT_EXPL_START 
   NORMAL_START
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
   #1;
   monitor.start_xactor();
   SING_DRV_END
   MULT_DRV_START
   begin `foreach_vmm_xactor(XACT, "/./", "/./") xact.start_xactor(); end  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   GEN_SL_RCVR_START
   receiver.start_xactor();
   GEN_SL_RCVR_END
   NORMAL_END
   XCT_EXPL_END
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
   //ToDo: Start the other components if added later
   

   NORMAL_START
   //ToDo: Register other components,channels and notifications if added by user  
   ATMC_GEN_START
   this.end_vote.register_xactor(this.atmc_gen);
   ATMC_GEN_END
   SCN_GEN_START  
   this.end_vote.register_xactor(this.scen_gen);
   SCN_GEN_END
   MS_GEN_START
   this.end_vote.register_xactor(this.gen_ms);
   MS_GEN_END
   SING_DRV_START
   this.end_vote.register_xactor(driver);
   SING_DRV_END
   MULT_DRV_START
   this.end_vote.register_xactor(driver_RPTNO);  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   NORMAL_END
NORMAL_START
endtask: start
NORMAL_END
MACRO_START
endtask: do_start
MACRO_END
TST_EXPL_END
TST_IMPL_START


task ENV::run_ph();
   super.run_ph();
   vote.wait_for_consensus();   //Waiting for the consensus to be reached
TST_IMPL_END
TST_EXPL_START


task ENV::wait_for_end();
   super.wait_for_end();
   end_vote.wait_for_consensus();   //Waiting for the consensus to be reached
TST_EXPL_END
TST_IMPL_START
endtask: run_ph
TST_IMPL_END
TST_EXPL_START
endtask: wait_for_end
TST_EXPL_END
TST_IMPL_START


task ENV::shutdown_ph();
   super.shutdown_ph();
   XCT_EXPL_START
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
   GEN_SL_RCVR_START
   receiver.stop_xactor();
   GEN_SL_RCVR_END 
   MULT_DRV_START
   begin   `foreach_vmm_xactor(XACT, "/./", "/./") xact.stop_xactor(); end //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   XCT_EXPL_END
   //ToDo: Stop the other components if added later
  
endtask:shutdown_ph
TST_IMPL_END
TST_EXPL_START
NORMAL_START


task ENV::stop();
   super.stop();
   XCT_IMPL_START
   env_tml.run_phase("shutdown");   
   XCT_IMPL_END
   XCT_EXPL_START
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
   GEN_SL_RCVR_START
   receiver.stop_xactor();
   GEN_SL_RCVR_END 
   MULT_DRV_START
   begin `foreach_vmm_xactor(XACT, "/./", "/./") xact.stop_xactor(); end //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   //ToDo: Stop the other components if added later

   XCT_EXPL_END 
endtask: stop
NORMAL_END
MACRO_START

task ENV::do_stop();
   XCT_IMPL_START
   env_tml.run_phase("shutdown");   
   XCT_IMPL_END
   //ToDo: Stop the other components if added later

endtask: do_stop
MACRO_END
TST_EXPL_END
TST_IMPL_START


task ENV::cleanup_ph();
   super.cleanup_ph();
   //ToDo: Shutdown the other components if added later

endtask: cleanup_ph
TST_IMPL_END
TST_EXPL_START


task ENV::cleanup();
   super.cleanup();
   XCT_IMPL_START
   env_tml.run_phase("cleanup");
   XCT_IMPL_END
endtask :cleanup
TST_EXPL_END
TST_IMPL_START


function void ENV::report_ph();
   super.report_ph();
   PERF_START
   this.monitor_perf_an.save_db();
   this.monitor_perf_an.report();
   this.driver_perf_an.save_db();
   this.driver_perf_an.report();
   PERF_END
   SCBD_EN_START
   sb.report();
   SCBD_EN_END
   //ToDo: call report method of other component if added later
endfunction: report_ph
TST_IMPL_END
TST_EXPL_START


task ENV::report();
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
   XCT_IMPL_START
   // ToDo: Generate the Final Report

   env_tml.run_phase("report");
   env_tml.run_phase("destruct");
   XCT_IMPL_END
endtask : report
TST_EXPL_END


// If mode is set to RECORD mode, transaction information is 
// dumped in a file. If mode is set to PLAYBACK mode, transaction 
// information is loaded from the file.
task automatic ENV::start_record_replay(vmm_channel chan, int i);
   fork begin
      string id_s = $psprintf("%0d", i);
      if (cfg.mode == CFG::RECORD) begin
		   `vmm_note(log,`vmm_sformatf("Recording Channel transaction in Chann%0d.dat file",i));
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

`endif // ENV__SV
