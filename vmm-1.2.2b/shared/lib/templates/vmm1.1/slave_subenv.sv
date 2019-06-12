//
// Template for VMM-compliant Sub-Environment
// <SLAVE_SE>   Name of Sub-environmnet class
// <REC>   Name of Slave/Receiver
//

`ifndef SLAVE_SE__SV
`define SLAVE_SE__SV

`include "REC.sv"

class SLAVE_SE_cfg;

   // ToDo: Add properties for configuring SLAVE_SE

endclass: SLAVE_SE_cfg


class SLAVE_SE extends vmm_subenv;

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
   MACRO_START

   // VMM Consensus handle
   vmm_consensus end_test;

   `vmm_subenv_member_begin(SLAVE_SE)
      `vmm_subenv_member_xactor(receiver, DO_ALL)
        // ToDo: add properties using macros here
   `vmm_subenv_member_end(SLAVE_SE)
   MACRO_END

   extern function new(string name = "",
                       string inst = "",
                       vmm_consensus end_test,
                       CFG cfg,
                       SING_DRV_START
                       virtual IF intf_inst,
                       SING_DRV_END
                       MULT_DRV_START
                       virtual IF intf_inst[INTF_COUNT],
                       MULT_DRV_END
                       SLAVE_SE_cfg se_cfg = null);
   extern task config_se();
   extern function build(); 
   NORMAL_START
   extern virtual task start();
   extern virtual task stop();
   NORMAL_END
   extern virtual task cleanup();
   extern virtual function void report();
endclass: SLAVE_SE


function SLAVE_SE::new (string name = "",
                        string inst = "",
                        vmm_consensus end_test,
                        CFG cfg,
                        SING_DRV_START
                        virtual IF intf_inst,
                        SING_DRV_END
                        MULT_DRV_START
                        virtual IF intf_inst[INTF_COUNT],
                        MULT_DRV_END
                        SLAVE_SE_cfg se_cfg = null);
   super.new(name,inst,end_test);
   if(se_cfg == null) se_cfg=new();  
   this.se_cfg = se_cfg;
   this.reset_cfg = se_cfg;
   this.end_test = end_test;
   // Save a copy of the configuration class
   this.cfg = cfg;
   // Save a copy of the interface instance
   this.intf_inst = intf_inst;

endfunction: new

function SLAVE_SE::build();   
   // ToDo : New all the sub environment components here.
   rcvr_chan = new("RCVR_CHANNEL", "");
   SING_DRV_START
   receiver  = new("SLAVE RECEIVER", 1, rcvr_chan,intf_inst); 
   SING_DRV_END
   MULT_DRV_START
   receiver  = new("SLAVE RECEIVER", 1, rcvr_chan,intf_inst[0]); 
   // ToDo : Add required instance of driver/monitor //Falguni: Temp, kept 
   MULT_DRV_END
endfunction: build


task SLAVE_SE::config_se();
   // ToDo: Configure sub env and portion of associated DUT if any

   super.configured();

endtask: config_se


NORMAL_START
task SLAVE_SE::start();
  super.start();
  // ToDo: Start all transactors in SLAVE_SE
  receiver.start_xactor();
endtask: start


task SLAVE_SE::stop();
  super.stop();
  // ToDo: Stop all generators 
  receiver.stop_xactor();
endtask: stop


NORMAL_END


task SLAVE_SE::cleanup();
   super.cleanup();
   
   // ToDo: Verify end-of-test conditions
endtask: cleanup


function void SLAVE_SE::report();
   super.report();
endfunction: report


`endif // SLAVE_SE__SV
