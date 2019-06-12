//
// Template for VMM-compliant Sub-Environment
// <MASTER_SE>  Name of Sub-environmnet class
// <SB>         Name of vmm_sb_ds Scoreboard class
// <CFG>        Name of the configuration class
// <TR>         Name of the transaction descriptor
// <XACT>       Name of the driver
// <MON>        Name of the monitor class
// <COV>        Name of the coverage class

`ifndef MASTER_SE__SV
`define MASTER_SE__SV
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


class MASTER_SE_cfg;

   `vmm_typename(MASTER_SE_cfg)
   // ToDo: Add properties for configuring MASTER_SE

endclass: MASTER_SE_cfg

XCT_IMPL_START
class MASTER_SE extends vmm_group;
XCT_IMPL_END
XCT_EXPL_START
class MASTER_SE extends vmm_subenv;
XCT_EXPL_END
   `vmm_typename(MASTER_SE)
   // VNAME configuration Instance 
   CFG cfg;
   SCBD_EN_START
   SB sb;
   SCBD_EN_END
   // VNAME Transaction Channel between Generator -> Master
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
   protected MASTER_SE_cfg mst_cfg;    // VNAME Sunenv configuration Instance 
   local MASTER_SE_cfg reset_cfg;
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
   MNTR_OBS_MTHD_ONE_START
   // ToDo : Add Callbacks  
 
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
   MON_perf_cb monitor_perf_cb;
   vmm_sql_db_ascii monitor_perf_db;
   vmm_perf_analyzer monitor_perf_an;
   vmm_sql_db_ascii driver_perf_db;
   vmm_perf_analyzer driver_perf_an;
   SING_DRV_START
   XACT_perf_cb driver_perf_cb;
   SING_DRV_END
   MULT_DRV_START
   XACT_perf_cb driver_perf_cb_RPTNO;   //VMMGEN_RPT_ON_XACT
   //ToDo: Instantiate other drivers callbacks here. 
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
   // ToDo: add sub environmnet properties here

   XCT_EXPL_START     
   // VMM Consensus handle
   vmm_consensus end_vote;
   XCT_EXPL_END


   XCT_EXPL_START
   MACRO_START
   // VMM shorthand macro which provides default implementation for
   // start/stop/reset xactor methods
   `vmm_subenv_member_begin(MASTER_SE)
      
      ATMC_GEN_START 
      `vmm_subenv_member_xactor(atmc_gen, DO_ALL)
      ATMC_GEN_END
      SCN_GEN_START
      `vmm_subenv_member_xactor(scen_gen, DO_ALL)
      SCN_GEN_END
      MS_GEN_START
      `vmm_subenv_member_xactor(gen_ms, DO_ALL)
      MS_GEN_END
      `vmm_subenv_member_xactor(monitor, DO_ALL)
      SING_DRV_START 
      `vmm_subenv_member_xactor(driver, DO_ALL)
      SING_DRV_END
      MULT_DRV_START
      `vmm_subenv_member_xactor(driver_RPTNO, DO_ALL)  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
      MNTR_OBS_MTHD_ONE_START
      `vmm_subenv_member_channel(mon_chan, DO_ALL)
      MNTR_OBS_MTHD_ONE_END
      `vmm_subenv_member_vmm_data(cfg, DO_ALL)
      // ToDo: add properties using macros here

   `vmm_subenv_member_end(MASTER_SE)
   MACRO_END
   XCT_EXPL_END
   MACRO_START
   XCT_IMPL_START 
   XCT_IMPL_END
   MACRO_END

   extern function new(string name, 
                       string inst,
                       vmm_consensus end_vote,
                       vmm_object parent=null,
                       MASTER_SE_cfg mst_cfg = null
                      );
   XCT_EXPL_START
   extern virtual function void configured();
   XCT_EXPL_END
   XCT_IMPL_START
   extern virtual function void build_ph();
   extern virtual function void configure_ph();
   extern virtual function void connect_ph();
   extern virtual function void start_of_sim_ph();
   extern virtual task reset_ph();
   extern virtual task config_dut_ph();
   extern virtual task start_ph();
   extern virtual task run_ph();
   extern virtual task shutdown_ph();
   extern virtual task cleanup_ph();
   extern virtual function void report_ph();
   XCT_IMPL_END
   extern virtual task start_record_replay(vmm_channel chan, int i);
   XCT_EXPL_START
   extern function void build();
   extern function void connect();
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   MACRO_START
   SCB_INT_MTHD_THREE_START
   extern virtual task do_start();
   SCB_INT_MTHD_THREE_END
   SCB_INT_MTHD_FOUR_START
   extern virtual task do_start();
   SCB_INT_MTHD_FOUR_END
   extern virtual task do_stop();
   MACRO_END
   extern virtual task cleanup();
   extern virtual function void report();
   XCT_EXPL_END

endclass: MASTER_SE


function MASTER_SE::new(string name, 
                        string inst,
                       vmm_consensus end_vote,
                       vmm_object parent=null,
                       MASTER_SE_cfg mst_cfg = null
                      );
  XCT_EXPL_START
   super.new(name, inst, end_vote,parent);
   this.end_vote = end_vote;
	XCT_EXPL_END
	XCT_IMPL_START
   super.new(name, inst, parent);
   vote = end_vote;
	XCT_IMPL_END
   if(mst_cfg == null) mst_cfg=new();  
   this.mst_cfg = mst_cfg;
   this.reset_cfg = mst_cfg;
	XCT_IMPL_START
	XCT_IMPL_END
   endfunction: new
XCT_IMPL_START


function void MASTER_SE::build_ph();
   MS_GEN_START
   // ToDo : Edit required constuctor argument here.
   gen_ms = new("Multistream Scenario Gen", 0,this);
   SING_DRV_START
   TR_chan = new("TR_channel_c","channel");  
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR_channel_cRPTNO","channel_RPTNO");  //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   MS_GEN_END
XCT_IMPL_END  
XCT_EXPL_START


function void MASTER_SE::build();
   MS_GEN_START
   // ToDo : Edit required constuctor argument here.
   gen_ms = new("Multistream Scenario Gen", 0,this);
   SING_DRV_START
   TR_chan = new("TR_channel_c","channel");  
   SING_DRV_END
   MULT_DRV_START
   TR_chan_RPTNO = new("TR_channel_cRPTNO","channel_RPTNO");  //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   MS_GEN_END
XCT_EXPL_END   
   MS_GEN_START
   SING_DRV_START
   gen_ms.register_channel("TR_scenario_channel", TR_chan); 
   SING_DRV_END
   MULT_DRV_START
   gen_ms.register_channel("TR_scenario_channel_RPTNO", TR_chan_RPTNO); //VMMGEN_RPT_ON_TR
   MULT_DRV_END
   //ToDo: Instantiate other required channels of required transaction types and register them
   
   XCT_EXPL_START
   ms_scn = VNAME_ms_scen::create_instance(this,"ms_scn"); 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   //ToDo: Register required scenarios

   XCT_EXPL_END
   MS_GEN_END
   ATMC_GEN_START
   XCT_IMPL_START
   atmc_gen = new("atmc_gen", 1,,this); 
   XCT_IMPL_END
   XCT_EXPL_START
   atmc_gen = new("atmc_gen", 1,,this); 
   XCT_EXPL_END
   ATMC_GEN_END
   SCN_GEN_START
   XCT_IMPL_START
   scen_gen = new("scen_gen", 1,,this); 
   XCT_IMPL_END
   XCT_EXPL_START
   scen_gen = new("scen_gen", 1,,this); 
   XCT_EXPL_END
   SCN_GEN_END
   // ToDo : Add appropriate argument in new() where allocating memory to component.
  
   FD_DRIV_START 
   DRIV_CHNL_START
   SING_DRV_START
   ATMC_GEN_START
   XCT_EXPL_START
   driver = new("Driver", "drv", 1,this, ,atmc_gen.out_chan);
   XCT_EXPL_END
   XCT_IMPL_START
   driver = new("Driver", "drv", 1, this, ,atmc_gen.out_chan);
   XCT_IMPL_END
	ATMC_GEN_END
	SCN_GEN_START
   XCT_EXPL_START
   driver = new("Driver", "drv", 1,this, ,scen_gen.out_chan);
   XCT_EXPL_END
   XCT_IMPL_START
   driver = new("Driver", "drv", 1, this, ,scen_gen.out_chan);
   XCT_IMPL_END
	SCN_GEN_END
   SING_DRV_END
   MULT_DRV_START
   // ToDo : User need to connect the channel
   XCT_IMPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO, this);  //VMMGEN_RPT_ON_XACT 
   XCT_IMPL_END
   XCT_EXPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO,this);  //VMMGEN_RPT_ON_XACT 
   XCT_EXPL_END
   MULT_DRV_END
   DRIV_CHNL_END
   DRIV_GEN_TLM_START
   SING_DRV_START
   XCT_IMPL_START
   driver = new("Driver","drv", 1, this); 
   XCT_IMPL_END
   XCT_EXPL_START  
   driver = new("Driver","drv", 1,this); 
   XCT_EXPL_END
   SING_DRV_END
   MULT_DRV_START
   XCT_IMPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, this);                 //VMMGEN_RPT_ON_XACT
   XCT_IMPL_END
   XCT_EXPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO,this);                 //VMMGEN_RPT_ON_XACT
   XCT_EXPL_END
   MULT_DRV_END
   DRIV_GEN_TLM_END
   FD_DRIV_END
   GNRC_DRIV_START 
   SING_DRV_START
   XCT_IMPL_START
   driver = new("Driver","drv", 1, this); 
   XCT_IMPL_END
   XCT_EXPL_START
   driver = new("Driver","drv", 1,this); 
   XCT_EXPL_END
   SING_DRV_END
   MULT_DRV_START
   XCT_IMPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", 1, this); //VMMGEN_RPT_ON_XACT
   XCT_IMPL_END
   XCT_EXPL_START
   driver_RPTNO = new("Driver_RPTNO","drv_RPTNO", RPTNO,this); //VMMGEN_RPT_ON_XACT
   XCT_EXPL_END
   MULT_DRV_END
   GNRC_DRIV_END
   MNTR_OBS_MTHD_ONE_START
   mon_chan     = new("Mon_TR_channel_c", "mon_chan");
   XCT_IMPL_START 
   monitor      = new("Monitor", "mon", 1, this, ,mon_chan); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor      = new("Monitor", "mon", 1,this, ,mon_chan); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_ONE_END 
   MNTR_OBS_MTHD_TWO_START
   XCT_IMPL_START 
   monitor      = new("Monitor","mon", 1, this); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor      = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START
   XCT_IMPL_START
   monitor = new("Monitor","mon", 1, this); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START
   XCT_IMPL_START
   monitor = new("Monitor","mon", 1, this); 
   XCT_IMPL_END
   XCT_EXPL_START
   monitor = new("Monitor","mon", 1,this); 
   XCT_EXPL_END
   MNTR_OBS_MTHD_FOUR_END
   cov = new();
   MNTR_OBS_MTHD_ONE_START
   mon2cov = new(cov);
   monitor.append_callback(mon2cov);
   MNTR_OBS_MTHD_ONE_END
   MNTR_OBS_MTHD_TWO_START
   MNTR_OBS_MTHD_TWO_Q_START
   mon2cov = new(cov);
   monitor.append_callback(mon2cov);
   MNTR_OBS_MTHD_TWO_Q_END
   MNTR_OBS_MTHD_TWO_END
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
      // ToDo: Add the shceme in create_table for monitors 
      
      vmm_sql_table monitor_perf_tbl = monitor_perf_db.create_table("TR", "");
      // ToDo: Insert the data string as per given scheme in create_table() instead of null string

      monitor_perf_tbl.insert("");
      monitor_perf_db.commit();
      //DISABLE PERFORMANCE-ANALYZER :Comment the following line to avoid the performance analyzer in monitor 
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
   sb = new("SCBD(GEN-MON)");
   bfm_sb_cb = new();              //Instance of Generator-Scoreboard callback
   SING_DRV_START 
   driver.append_callback(bfm_sb_cb); //Appending the callback with driver
   SING_DRV_END
   MULT_DRV_START
   driver_0.append_callback(bfm_sb_cb);  
   MULT_DRV_END
   SCBD_EN_END 
   // ToDo: Register any required callbacks

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
XCT_EXPL_START
  this.configured();
 endfunction: build
XCT_EXPL_END
XCT_IMPL_START   
endfunction: build_ph


function void MASTER_SE::configure_ph();
   //ToDo : functional configuration if needed 
   if(this.cfg != null) begin
     `vmm_note(log, "configure_ph executed");
   end

endfunction: configure_ph
XCT_IMPL_END
XCT_EXPL_START


//This function is called from ENV::build_phase
function void MASTER_SE::configured();
   super.configured();
   if(this.cfg != null) begin
     `vmm_note(log, "configured() executed");
   end
endfunction : configured
XCT_EXPL_END
XCT_IMPL_START


function void MASTER_SE::connect_ph();
   super.connect_ph();
 XCT_IMPL_END
XCT_EXPL_START


function void MASTER_SE::connect();
XCT_EXPL_END
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
   vmm_connect#(,,TR)::tlm_bind(atmc_gen.out_chan,driver.drv_b_export,vmm_tlm::TLM_BLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(,,TR)::tlm_bind(scen_gen.out_chan,driver.drv_b_export,vmm_tlm::TLM_BLOCKING_PORT);
	SCN_GEN_END
   DRIV_TLM_B_TRANS_EX_END
   DRIV_TLM_NB_TRANS_FW_EX_START
	ATMC_GEN_START
   vmm_connect#(,,TR)::tlm_bind(atmc_gen.out_chan,driver.drv_nb_export,vmm_tlm::TLM_NONBLOCKING_FW_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(,,TR)::tlm_bind(scen_gen.out_chan,driver.drv_nb_export,vmm_tlm::TLM_NONBLOCKING_FW_PORT);
	SCN_GEN_END
   DRIV_TLM_NB_TRANS_FW_EX_END
   DRIV_TLM_NB_TRANS_EX_START
	ATMC_GEN_START
   vmm_connect#(,,TR)::tlm_bind(atmc_gen.out_chan,driver.drv_nb_bidir,vmm_tlm::TLM_NONBLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(,,TR)::tlm_bind(scen_gen.out_chan,driver.drv_nb_bidir,vmm_tlm::TLM_NONBLOCKING_PORT);
	SCN_GEN_END
   DRIV_TLM_NB_TRANS_EX_END
   DRIV_TLM_SMPL_TRGT_SCKT_START
	ATMC_GEN_START
   vmm_connect#(,,TR)::tlm_bind(atmc_gen.out_chan,driver.drv_target_exp,vmm_tlm::TLM_NONBLOCKING_PORT);
	ATMC_GEN_END
	SCN_GEN_START
   vmm_connect#(,,TR)::tlm_bind(scen_gen.out_chan,driver.drv_target_exp,vmm_tlm::TLM_NONBLOCKING_PORT);
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
   MNTR_OBS_MTHD_THREE_START
   SCBD_EN_START 
   this.mon_2_subs_cb.mon2sub_analys_port.tlm_bind(sb.exp_ap);            
   SCBD_EN_END
   this.mon_2_subs_cb.mon2sub_analys_port.tlm_bind(cov.cov_export);       
   MNTR_OBS_MTHD_THREE_END
   SCBD_EN_START 
   //Connecting the BFM callback's analysis port with SB's input analysis export.
   this.bfm_sb_cb.bfm_analysis_port.tlm_bind(sb.inp_ap);
   SCBD_EN_END 
   XCT_EXPL_START
endfunction: connect
   XCT_EXPL_END
XCT_IMPL_START
endfunction: connect_ph


function void MASTER_SE::start_of_sim_ph();
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


task MASTER_SE::reset_ph();
   // ToDo: Reset DUT

endtask : reset_ph


task MASTER_SE::config_dut_ph();
   super.config_dut_ph();
   MS_GEN_START
   ms_scn = VNAME_ms_scen::create_instance(this,"ms_scn"); 
   gen_ms.register_ms_scenario("scenario_0", ms_scn);
   MS_GEN_END
   // ToDo: Configure the DUT

endtask : config_dut_ph


task MASTER_SE::start_ph();
   ATMC_GEN_START
   this.vote.register_xactor(this.atmc_gen);
   ATMC_GEN_END
   SCN_GEN_START  
   this.vote.register_xactor(this.scen_gen);
   SCN_GEN_END
   MS_GEN_START
   this.vote.register_xactor(this.gen_ms);
   MS_GEN_END
   SING_DRV_START
   this.vote.register_xactor(driver);
   SING_DRV_END
   MULT_DRV_START
   this.vote.register_xactor(driver_RPTNO);  //VMMGEN_RPT_ON_XACT
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
   //ToDo: Start the other components if added later

endtask: start_ph
XCT_IMPL_END
XCT_EXPL_START
NORMAL_START


task MASTER_SE::start();
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
   #1;
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
   this.end_vote.register_xactor(this.driver);
   SING_DRV_END
   MULT_DRV_START
   this.end_vote.register_xactor(this.driver_RPTNO);  //VMMGEN_RPT_ON_XACT
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
   //ToDo: Start the other components if added later

   end_vote.wait_for_consensus();  //Waiting for the consensus to be reached
endtask: start


task MASTER_SE::stop();
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
endtask: stop
NORMAL_END
MACRO_START
SCB_INT_MTHD_THREE_START


task MASTER_SE::do_start();
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


task MASTER_SE::do_stop();
   //ToDo:Stop the components which are started

endtask: do_stop
MACRO_END
XCT_EXPL_END
XCT_IMPL_START


task MASTER_SE::run_ph();
   vote.wait_for_consensus();   //Waiting for the consensus to be reached
endtask: run_ph


task MASTER_SE::shutdown_ph();
   //ToDo:Add the components which are started

endtask: shutdown_ph


task MASTER_SE::cleanup_ph();
   // ToDo: check that nothing was lost
endtask: cleanup_ph
XCT_IMPL_END
XCT_EXPL_START


task MASTER_SE::cleanup();
endtask: cleanup
XCT_EXPL_END
XCT_IMPL_START


function void MASTER_SE::report_ph();
XCT_IMPL_END
XCT_EXPL_START


function void MASTER_SE::report();
XCT_EXPL_END
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

XCT_EXPL_START
endfunction: report
XCT_EXPL_END
XCT_IMPL_START
endfunction: report_ph
XCT_IMPL_END


// If mode is set to RECORD mode, transaction information is 
// dumped in a file. If mode is set to PLAYBACK mode, transaction 
// information is loaded from the file.
task MASTER_SE::start_record_replay(vmm_channel chan, int i);
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

`endif // MASTER_SE__SV

