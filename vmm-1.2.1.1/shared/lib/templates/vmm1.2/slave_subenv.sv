// Template for VMM-compliant Sub-Environment
// <SLAVE_SE>   Name of Sub-environmnet class
// <REC>   Name of Slave/Receiver
//

`ifndef SLAVE_SE__SV
`define SLAVE_SE__SV

`include "REC.sv"

class SLAVE_SE_cfg;

   `vmm_typename(SLAVE_SE_cfg)
   // ToDo: Add properties for configuring SLAVE_SE

endclass: SLAVE_SE_cfg

XCT_IMPL_START
class SLAVE_SE extends vmm_group;
XCT_IMPL_END
XCT_EXPL_START
class SLAVE_SE extends vmm_subenv;
XCT_EXPL_END

   `vmm_typename(SLAVE_SE)
   // VNAME Sunenv configuration Instance
   protected SLAVE_SE_cfg se_cfg;   
   local SLAVE_SE_cfg reset_cfg;
   REC receiver;
   TR_channel rcvr_chan;
   // VNAME Virtual Interface Instance
   SING_DRV_START
   virtual IF intf_inst;
   SING_DRV_END
   MULT_DRV_START
   virtual IF intf_inst[INTF_COUNT];
   MULT_DRV_END
   // VNAME configuration Instance 
   CFG cfg;
   // ToDo: add sub environmnet properties here

   XCT_EXPL_START
    // VMM Consensus handle
   vmm_consensus end_vote;
   XCT_EXPL_END
   XCT_EXPL_START
   MACRO_START
   `vmm_subenv_member_begin(SLAVE_SE)
      `vmm_subenv_member_xactor(receiver, DO_ALL)
       // ToDo: add properties using macros here
   
   `vmm_subenv_member_end(SLAVE_SE)
   MACRO_END
   XCT_EXPL_END
   MACRO_START
   XCT_IMPL_START 
   XCT_IMPL_END
   MACRO_END
	
   extern function new(string name = "Slave SubEnv",
                       string inst,
                       vmm_consensus end_vote,
                       vmm_object parent=null
                      );
	XCT_EXPL_START
   extern virtual function void configured();
	XCT_EXPL_END
   extern virtual task start_record_replay(vmm_channel chan, int i);
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
   XCT_EXPL_START
   extern function void build();
   extern function void connect();
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   MACRO_START
   extern virtual task do_start();
   extern virtual task do_stop();
   MACRO_END
   extern virtual task cleanup();
   extern virtual function void report();
   XCT_EXPL_END

endclass: SLAVE_SE


function SLAVE_SE::new (string name = "Slave SubEnv",
                       string inst,
                       vmm_consensus end_vote,
                       vmm_object parent=null
                        );
   XCT_EXPL_START
   super.new(name, inst, end_vote,parent);
   this.end_vote = end_vote;
	XCT_EXPL_END
	XCT_IMPL_START
   super.new(name, inst, parent);
   vote = end_vote;
	XCT_IMPL_END
endfunction: new
XCT_IMPL_START


function void SLAVE_SE::build_ph();
   super.build_ph();
   cfg = new();
XCT_IMPL_END
XCT_EXPL_START


function void SLAVE_SE::build();
XCT_EXPL_END   
   // ToDo : New all the sub environment components here.

   rcvr_chan = new("RCVR_CHANNEL", "");
   SING_DRV_START
   receiver  = new("SLAVE RECEIVER","rec", 1, rcvr_chan,this); 
   SING_DRV_END
   MULT_DRV_START
   receiver  = new("SLAVE RECEIVER","rec", 1, rcvr_chan,this); 
   // ToDo : Add required instance of driver/monitor  

   MULT_DRV_END
XCT_EXPL_START
  this.configured();
endfunction: build
XCT_EXPL_END
XCT_IMPL_START    
endfunction: build_ph


function void SLAVE_SE::configure_ph();
   super.configure_ph();
   //ToDo : functional configuration if needed 

endfunction: configure_ph
XCT_IMPL_END


XCT_EXPL_START
//This function is called from ENV::build_phase
function void SLAVE_SE::configured();
   super.configured();
   if(this.cfg != null) begin
     `vmm_note(log, "configured() executed");
   end
endfunction : configured
XCT_EXPL_END
XCT_IMPL_START


function void SLAVE_SE::connect_ph();
   super.connect_ph();
   //ToDo : functional configuration if needed

endfunction: connect_ph


function void SLAVE_SE::start_of_sim_ph();
   super.start_of_sim_ph();
endfunction: start_of_sim_ph
XCT_IMPL_END
XCT_EXPL_START


function void SLAVE_SE::connect();
   //ToDo : functional configuration if needed

endfunction: connect
XCT_EXPL_END
XCT_IMPL_START


task SLAVE_SE::reset_ph();
   super.reset_ph();
   //ToDo: Reset DUT

endtask : reset_ph


task SLAVE_SE::config_dut_ph();
   super.config_dut_ph();
   //ToDo: Configure the DUT

endtask : config_dut_ph


task SLAVE_SE::start_ph();
   super.start_ph();
   //ToDo: Start the other components if added later

endtask: start_ph 
XCT_IMPL_END
XCT_EXPL_START
NORMAL_START


task SLAVE_SE::start();
   receiver.start_xactor();
   end_vote.wait_for_consensus();//Waiting for the consensus to be reached
endtask: start


task SLAVE_SE::stop();
   receiver.stop_xactor();
endtask: stop
NORMAL_END
MACRO_START


task SLAVE_SE::do_start();
   //ToDo: Start the other components if added later

endtask: do_start


task SLAVE_SE::do_stop();
   //ToDo: Stop the other components if added later 

endtask: do_stop
MACRO_END
XCT_EXPL_END
XCT_IMPL_START


task SLAVE_SE::run_ph();
   super.run_ph();
   vote.wait_for_consensus();//Waiting for the consensus to be reached
endtask: run_ph


task SLAVE_SE::shutdown_ph();
   super.shutdown_ph();
   //ToDo: Stop the other explicit components if added later
endtask: shutdown_ph


task SLAVE_SE::cleanup_ph();
   super.cleanup_ph();
	//ToDo: Shutdown the other components if added later
endtask: cleanup_ph


function void SLAVE_SE::report_ph();
   super.report_ph();
   // ToDo: Generate the Final Report

endfunction: report_ph
XCT_IMPL_END
XCT_EXPL_START


task SLAVE_SE::cleanup();
endtask: cleanup


function void SLAVE_SE::report();
   // ToDo: Generate the Final Report

endfunction: report
XCT_EXPL_END


// If mode is set to RECORD mode, transaction information is 
// dumped in a file. If mode is set to PLAYBACK mode, transaction 
// information is loaded from the file.
task SLAVE_SE::start_record_replay(vmm_channel chan, int i);
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

`endif // SLAVE_SE__SV
