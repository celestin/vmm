//
// Template for VMM-compliant verification environment
// <VNAME>     Name of VIP
// <ENV>       Name of Environment class
// <MASTER_SE> Name of Master Sub Environment class
// <SLAVE_SE>  Name of Slave Sub Environment class
// <IF>        Name of Interface
// <CFG>       Name of the configuration class
// <XACT>      Name of the Driver
// <REC>       Name of Slave Receiver
// <TR>        Name of the transaction descriptor
// <SB>        Name of vmm_sb_ds Scoreboard class
// <MON>       Name of the monitor class
// <COV>       Name of the coverage class
// [filename]  ENV
//

`ifndef ENV__SV
`define ENV__SV

//Including all the required files here
`include "VNAME.sv"
//ToDo: Include required files here
//Including the master and slave  subenvironment files
`include "MASTER_SE.sv"
GEN_SL_RCVR_START
`include "SLAVE_SE.sv"
GEN_SL_RCVR_END

RAL_START
class ENV extends vmm_ral_env;
RAL_END
COMMON_START
class ENV extends vmm_env;
COMMON_END
   // Instance of Interface
   SING_DRV_START
   virtual IF intf_inst;
   SING_DRV_END
   MULT_DRV_START
   virtual IF intf_inst[INTF_COUNT];
   MULT_DRV_END

   RAL_START

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

   // Instance of Test config
   CFG cfg;   

   // Instance of Master Sub env
   MASTER_SE mast_subenv;
   
   GEN_SL_RCVR_START
   // Instance of Slave Sub env
   SLAVE_SE slv_subenv;            
   GEN_SL_RCVR_END
   RAL_START

   ral_block_VNAME ral_model;
   RAL_END
   MACRO_START
   
   `vmm_env_member_begin(ENV)
     `vmm_env_member_subenv(mast_subenv, DO_ALL)
      RAL_START
      MULT_DM_START
     `vmm_env_member_xactor(DN1_host, DO_ALL)
     `vmm_env_member_xactor(DN2_host, DO_ALL)
      MULT_DM_END
      SING_DM_START
     `vmm_env_member_xactor(host, DO_ALL)
      SING_DM_END
      RAL_END
      GEN_SL_RCVR_START
     `vmm_env_member_subenv(slv_subenv , DO_ALL)
      GEN_SL_RCVR_END
      // ToDo: Add required vmm env member
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
   this.cfg       = new;
   mast_subenv    = new("MASTER SUB ENV","",end_vote,cfg,intf_inst);
   GEN_SL_RCVR_START
   slv_subenv     = new("SLAVE SUB ENV","",end_vote,cfg,intf_inst);
   GEN_SL_RCVR_END
   $timeformat(-9, 0, "ns", 1);
   RAL_START
   this.ral_model = new();
   super.ral.set_model(this.ral_model);
   RAL_END
   $timeformat(-9, 0, "ns", 1);

endfunction: new


function void ENV::gen_cfg();
   MACRO_START
   string md;
   MACRO_END
   super.gen_cfg();

   if (!this.cfg.randomize()) begin
      `vmm_fatal(log, "Failed to randomize test configuration");
   end
   mast_subenv.config_se();
   GEN_SL_RCVR_START
   slv_subenv.config_se();
   GEN_SL_RCVR_END

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
   mast_subenv.build();   //Calling the build of Master Sub Env
   GEN_SL_RCVR_START
   slv_subenv.build();    //Calling the build of Slave Sub Env 
   GEN_SL_RCVR_END
   RAL_START
   MULT_DM_START
   SING_DRV_START
   this.DN1_host = new("RAL DN1 BFM","DN1_host",0,mast_subenv.driver);
   SING_DRV_END
   MULT_DRV_START
   this.DN1_host = new("RAL DN1 BFM","DN1_host",0,mast_subenv.driver_0);
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


task ENV::reset_dut();
   super.reset_dut();

   // ToDo: Apply hardware reset to DUT
endtask: reset_dut

   
task ENV::cfg_dut();
   super.cfg_dut();

   // ToDo: Configure DUT
endtask: cfg_dut
NORMAL_START


task ENV::start();
   super.start();
   mast_subenv.start();
   GEN_SL_RCVR_START
   slv_subenv.start();
   GEN_SL_RCVR_END

endtask: start


task ENV::stop();
   super.stop();
   mast_subenv.stop();      
   GEN_SL_RCVR_START
   slv_subenv.stop();
   GEN_SL_RCVR_END
endtask: stop
NORMAL_END


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
   mast_subenv.report();
   GEN_SL_RCVR_START
   slv_subenv.report();
   GEN_SL_RCVR_END
endtask: report

`endif // ENV__SV
