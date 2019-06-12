//
// Template for VMM-compliant verification environment
// <VNAME>     Name of VIP
// <ENV>       Name of Environment class
// <MASTER_SE> Name of Master Sub Environment class
// <SLAVE_SE>  Name of Slave Sub Environment class
// <IF>        Name of Interface
// <CFG>       Name of the configuration class
// <XACT>      Name of the Driver
// <TR>        Name of the transaction descriptor
// <SB>        Name of vmm_sb_ds Scoreboard class
// <MON>       Name of the monitor class
// <COV>       Name of the coverage class
// <REC>       Name of the slave reciever class
// [filename]  ENV
//

`ifndef ENV__SV
`define ENV__SV

//Including all the required component file names here
`include "VNAME.sv"
//ToDo: Include required files here
//Including the master and slave  subenvironment files
`include "MASTER_SE.sv"
GEN_SL_RCVR_START
`include "SLAVE_SE.sv"
GEN_SL_RCVR_END
RAL_START
TST_EXPL_START

class ENV extends vmm_ral_env;
TST_EXPL_END
TST_IMPL_START

class ENV extends vmm_group;
TST_IMPL_END
RAL_END
COMMON_START
TST_EXPL_START

class ENV extends vmm_env;

TST_EXPL_END
TST_IMPL_START
class ENV extends vmm_group;

   `vmm_typename(ENV)
TST_IMPL_END
COMMON_END
   RAL_START
   ral_block_VNAME ral_model;
   TST_IMPL_START
   vmm_ral_access  ral;
   TST_IMPL_END
   MULT_DM_START
   //ToDo : Instantiate other RAL BFMs, if more than two domains are used.
   XACT_DN1_ral DN1_host;
   XACT_DN2_ral DN2_host;
   MULT_DM_END
   SING_DM_START
   // Instance of RAL access transactor
   XACT_ral host;
   SING_DM_END
   RAL_END
   CFG cfg;  
   MASTER_SE mast_subenv;  // Instance of Master Sub env
   GEN_SL_RCVR_START
   SLAVE_SE slv_subenv;  // Instance of Slave Sub env          
   GEN_SL_RCVR_END
   TST_EXPL_START
   XCT_IMPL_START
   vmm_timeline env_tml;
   XCT_IMPL_END
   TST_EXPL_END
   RTLCFG_START 
   env_config  env_cfg;
   RTLCFG_END 

   MACRO_START
   TST_EXPL_START 
   `vmm_env_member_begin(ENV)
	   XCT_EXPL_START
      `vmm_env_member_subenv(mast_subenv, DO_ALL)
	   XCT_EXPL_END
      RAL_START
      MULT_DM_START
      `vmm_env_member_xactor(DN1_host, DO_ALL)
      `vmm_env_member_xactor(DN2_host, DO_ALL)
      MULT_DM_END
      SING_DM_START
      `vmm_env_member_xactor(host, DO_ALL)
      SING_DM_END
      RAL_END
      XCT_EXPL_START
      GEN_SL_RCVR_START
      `vmm_env_member_subenv(slv_subenv , DO_ALL)
      GEN_SL_RCVR_END
      XCT_EXPL_END
      // ToDo: Add required vmm env member
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
   extern virtual function void start_of_sim_ph();
   extern virtual task reset_ph();
   extern virtual task config_dut_ph();
   extern virtual task start_ph();
   extern virtual task run_ph();
   extern virtual task shutdown_ph();
   extern virtual task cleanup_ph();
   extern virtual function void report_ph();
   TST_IMPL_END
   extern virtual task start_record_replay(vmm_channel chan, int i);
   RAL_START
   extern virtual task hw_reset();
   RAL_END
   TST_EXPL_START
   extern function new(string name);
   extern virtual function void gen_cfg();
   extern virtual function void build();
   extern virtual task reset_dut();
   extern virtual task cfg_dut();
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   extern virtual task wait_for_end();
   extern virtual task cleanup();
   extern virtual task report();
   MACRO_START
   extern virtual task do_start();
   extern virtual task do_stop();
   MACRO_END
   TST_EXPL_END

endclass: ENV
TST_IMPL_START


function ENV::new(string name, vmm_group parent=null);
   super.new(name,"env",parent);
TST_IMPL_END
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
   $timeformat(-9, 0, "ns", 1);
endfunction: new
TST_EXPL_START


function void ENV::gen_cfg();
   MACRO_START
   string md;
   MACRO_END
   super.gen_cfg();
   if (!this.cfg.randomize()) begin
      `vmm_fatal(log, "Failed to randomize test configuration");
   end
   cfg.display("ENV config");
   //ToDo : functional configuration if needed
endfunction:gen_cfg
TST_EXPL_END
TST_EXPL_START


function void ENV::build();
   super.build();
   XCT_IMPL_START
   env_tml = new("ENV timeline","env_tml",this);
   mast_subenv    = new("MASTER SUB ENV","mast_subenv",end_vote,env_tml);
   GEN_SL_RCVR_START
   slv_subenv     = new("SLAVE SUB ENV","slv_subenv",end_vote,env_tml);
   GEN_SL_RCVR_END
   XCT_IMPL_END
   XCT_EXPL_START
   mast_subenv    = new("MASTER SUB ENV","mast_subenv",end_vote,this);
   GEN_SL_RCVR_START
   slv_subenv     = new("SLAVE SUB ENV","slv_subenv",end_vote,this);
   GEN_SL_RCVR_END
   mast_subenv.cfg = this.cfg;
   mast_subenv.build();   //Calling the build of Master Sub Env
   GEN_SL_RCVR_START
   slv_subenv.cfg = this.cfg;
   slv_subenv.build();    //Calling the build of Slave Sub Env 
   GEN_SL_RCVR_END
   XCT_EXPL_END
   RAL_START
   this.ral_model = new();
   super.ral.set_model(this.ral_model);
   MULT_DM_START
   SING_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,mast_subenv.driver);
   SING_DRV_END
   MULT_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,mast_subenv.driver_0);
   MULT_DRV_END
   super.ral.add_xactor(this.DN1_host);  //ToDo: User need to pass the domain name in second argument.
   //ToDo: User need to instantiate the other RAL BFMs and add them in the RAL access instance
   //e.g.
   //this.DN2_host = new("RAL DN2 BFM",0,<instance of other physical driver>);
   //super.ral.add_xactor(this.DN2_host,<Domain Name>); 
   MULT_DM_END
   SING_DM_START
   SING_DRV_START
   this.host = new("RAL BFM","host",0,mast_subenv.driver);
   SING_DRV_END
   MULT_DRV_START
   this.host = new("RAL BFM","host",0,mast_subenv.driver_0);
   MULT_DRV_END
   super.ral.add_xactor(this.host);
   SING_DM_END
   RAL_END
endfunction: build
TST_EXPL_END
TST_IMPL_START


function void ENV::build_ph();
   super.build_ph();
   XCT_IMPL_START
   mast_subenv    = new("MASTER SUB ENV","mast_subenv",vote,this);
   GEN_SL_RCVR_START
   slv_subenv     = new("SLAVE SUB ENV","slv_subenv",vote,this);
   GEN_SL_RCVR_END
   XCT_IMPL_END
   XCT_EXPL_START
   mast_subenv    = new("MASTER SUB ENV","mast_subenv",vote,this);
   GEN_SL_RCVR_START
   slv_subenv     = new("SLAVE SUB ENV","slv_subenv",vote,this);
   GEN_SL_RCVR_END
   XCT_EXPL_END
   XCT_EXPL_START 
   mast_subenv.build();   //Calling the build of Master Sub Env
   GEN_SL_RCVR_START
   slv_subenv.build();    //Calling the build of Slave Sub Env 
   GEN_SL_RCVR_END
   XCT_EXPL_END
   RTLCFG_START
   env_cfg.map_to_name("^");
   SING_DRV_START
   env_cfg.mst_cfg.map_to_name("env:mast_subenv:drv");
   SING_DRV_END
   MULT_DRV_START
   env_cfg.mst_cfg_RPTNO.map_to_name("env:mast_subenv:drv_RPTNO");  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   GEN_SL_RCVR_START
   env_cfg.slv_cfg.map_to_name("env:slv_subenv:rec");
   GEN_SL_RCVR_END
   //ToDo : Add the mapping if any other RTL config objects are defined.
   RTLCFG_END
   RAL_START
   this.ral_model = new();
   this.ral = new(this, "ral");
   this.ral.set_model(this.ral_model);
   MULT_DM_START
   SING_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,mast_subenv.driver);
   SING_DRV_END
   MULT_DRV_START
   this.DN1_host = new("RAL DN1 BFM","",0,mast_subenv.driver_0);
   MULT_DRV_END
   this.ral.add_xactor(this.DN1_host);  //ToDo: User need to pass the domain name in second argument.
   //ToDo: User need to instantiate the other RAL BFMs and add them in the RAL access instance
   //e.g.
   //this.DN2_host = new("RAL DN2 BFM",0,<instance of other physical driver>);
   //this.ral.add_xactor(this.DN2_host,"<Domain Name>");
   MULT_DM_END
   SING_DM_START
   SING_DRV_START
   this.host = new("RAL BFM","host",0,mast_subenv.driver);
   SING_DRV_END
   MULT_DRV_START
   this.host = new("RAL BFM","host",0,mast_subenv.driver_0);
   MULT_DRV_END
   this.ral.add_xactor(this.host);
   SING_DM_END 
   RAL_END
endfunction: build_ph
TST_IMPL_END
TST_IMPL_START


function void ENV::configure_ph();
   bit is_set; 
   super.configure_ph();
 endfunction: configure_ph
TST_IMPL_END
TST_IMPL_START


function void ENV::connect_ph();
   super.connect_ph();
   //ToDo : functional configuration if needed 

   //Printing the complete hierarchy of env
   print_hierarchy();
endfunction: connect_ph
TST_IMPL_END
TST_IMPL_START


task ENV::reset_ph();
   super.reset_ph();
   //ToDo: Reset DUT
endtask : reset_ph
TST_IMPL_END
TST_EXPL_START


task ENV::reset_dut();
   super.reset_dut();
   XCT_IMPL_START
   env_tml.run_phase("build");
   env_tml.run_phase("configure");
   env_tml.run_phase("connect");
   // ToDo: Apply hardware reset to DUT 
   //Master and slave subenv's connect method which makes connections
   XCT_EXPL_START
   mast_subenv.connect();
   slv_subenv.connect();
   XCT_EXPL_END
   env_tml.run_phase("start_of_sim");
   env_tml.run_phase("reset");
   env_tml.run_phase("training");
   XCT_IMPL_END
   XCT_EXPL_START
   // ToDo: Apply hardware reset to DUT 
    
   XCT_EXPL_END
endtask: reset_dut
TST_EXPL_END
RAL_START


task ENV::hw_reset();
   // ToDo: Apply hardware reset to DUT

endtask: hw_reset
RAL_END
TST_EXPL_START


task ENV::cfg_dut();
   super.cfg_dut();
   // ToDo: Configure DUT

   XCT_IMPL_START 
   env_tml.run_phase("config_dut");
   XCT_IMPL_END
endtask: cfg_dut
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
   
   //Passing the config. to the master and slave subenv
   vmm_opts::set_object("mast_subenv:cfg",cfg,this);
   GEN_SL_RCVR_START
   vmm_opts::set_object("slv_subenv:cfg",cfg,this);
   GEN_SL_RCVR_END
endfunction: start_of_sim_ph
TST_IMPL_END
TST_IMPL_START


task ENV::start_ph();
   super.start_ph();
   //ToDo: Start the other components if added later
   XCT_EXPL_START 
   mast_subenv.start();
   GEN_SL_RCVR_START
   slv_subenv.start();
   GEN_SL_RCVR_END
   XCT_EXPL_END
	//ToDo: register explicit component as voter for end of test
endtask: start_ph 
TST_IMPL_END
TST_IMPL_START


task ENV::config_dut_ph();
   super.config_dut_ph();
   //ToDo: Configure the DUT
endtask : config_dut_ph
TST_IMPL_END
TST_EXPL_START
NORMAL_START


task ENV::start();
   super.start();
   XCT_EXPL_START 
   mast_subenv.start();
   GEN_SL_RCVR_START
   slv_subenv.start();
   GEN_SL_RCVR_END
   XCT_EXPL_END
   XCT_IMPL_START 
   env_tml.run_phase("start");
   env_tml.run_phase("start_of_test");
   env_tml.run_phase("run_test");
   XCT_IMPL_END
endtask: start
NORMAL_END
MACRO_START


task ENV::do_start() ;
   XCT_IMPL_START 
   env_tml.run_phase("start");
   env_tml.run_phase("start_of_test");
   env_tml.run_phase("run_test");
   XCT_IMPL_END
endtask : do_start
MACRO_END
TST_EXPL_END
TST_IMPL_START


task ENV::run_ph();
   super.run_ph();
   //ToDo: wait for end of test vote of explicit components
   this.vote.wait_for_consensus();
TST_IMPL_END
TST_EXPL_START


task ENV::wait_for_end();
   super.wait_for_end();
   this.end_vote.wait_for_consensus();
TST_EXPL_END
TST_IMPL_START
endtask: run_ph
TST_IMPL_END
TST_EXPL_START
endtask: wait_for_end
TST_EXPL_END
TST_EXPL_START
NORMAL_START


task ENV::stop();
   super.stop();
   XCT_EXPL_START
   mast_subenv.stop();      
   GEN_SL_RCVR_START
   slv_subenv.stop();
   GEN_SL_RCVR_END
   XCT_EXPL_END
   XCT_IMPL_START
   env_tml.run_phase("shutdown");
   XCT_IMPL_END
endtask: stop
NORMAL_END
MACRO_START


task ENV::do_stop();
   XCT_IMPL_START
   env_tml.run_phase("shutdown");
   XCT_IMPL_END
endtask
MACRO_END
TST_EXPL_END
TST_IMPL_START


task ENV::shutdown_ph();
   super.shutdown_ph();
   XCT_EXPL_START
   mast_subenv.stop();      
   GEN_SL_RCVR_START
   slv_subenv.stop();
   GEN_SL_RCVR_END
   XCT_EXPL_END
  //ToDo: Shutdown the other components if added later
endtask: shutdown_ph
TST_IMPL_END
TST_EXPL_START


task ENV::cleanup();
   super.cleanup();
   XCT_EXPL_START
   mast_subenv.cleanup();      
   GEN_SL_RCVR_START
   slv_subenv.cleanup();
   GEN_SL_RCVR_END
   XCT_EXPL_END
   // ToDo: check that nothing was lost
   XCT_IMPL_START 
   env_tml.run_phase("cleanup");
   XCT_IMPL_END
endtask: cleanup
TST_EXPL_END
TST_IMPL_START


task ENV::cleanup_ph();
   super.cleanup_ph();
   XCT_EXPL_START
   mast_subenv.cleanup();      
   GEN_SL_RCVR_START
   slv_subenv.cleanup();
   GEN_SL_RCVR_END
   XCT_EXPL_END
   // ToDo: check that nothing was lost
endtask: cleanup_ph
TST_IMPL_END
TST_IMPL_START


function void ENV::report_ph();
   super.report_ph();
   XCT_EXPL_START
   mast_subenv.report();
   GEN_SL_RCVR_START
   slv_subenv.report();
   GEN_SL_RCVR_END
   XCT_EXPL_END
	//ToDo: Call report() method of other explicit component/subenv if added later
endfunction: report_ph
TST_IMPL_END
TST_EXPL_START


task ENV::report() ;
   super.report();
   XCT_EXPL_START
   mast_subenv.report();
   GEN_SL_RCVR_START
   slv_subenv.report();
   GEN_SL_RCVR_END
   XCT_EXPL_END
   XCT_IMPL_START 
   env_tml.run_phase("report");
   env_tml.run_phase("destruct");
   XCT_IMPL_END
endtask: report
TST_EXPL_END


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

`endif // ENV__SV
