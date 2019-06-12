//
// Template for VMM-compliant Sub-Environment
// <SE>            Name of Sub-environmnet class
//

`ifndef SE__SV
`define SE__SV

class SE_cfg;

   `vmm_typename(SE_cfg)
   // ToDo: Add properties for configuring SE

endclass: SE_cfg


XCT_EXPL_START
class SE extends vmm_subenv;
XCT_EXPL_END
XCT_IMPL_START
class SE extends vmm_group;
XCT_IMPL_END

   `vmm_typename(SE)
   SE_cfg      cfg;
   // ToDo: add sub environmnet properties here


XCT_EXPL_START
MACRO_START
   `vmm_subenv_member_begin(SE)
      // ToDo: add properties using macros here

   `vmm_subenv_member_end(SE)
      // ToDo: Add required short hand override method
MACRO_END
XCT_EXPL_END

   extern function new(string name = "",
                       string inst = "", 
                       vmm_consensus end_test,
                       SE_cfg cfg = null);
XCT_EXPL_START
   extern virtual function void configured();   
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
XCT_IMPL_START
   extern virtual task config_dut_ph();
   extern virtual task start_ph();  
   extern virtual task shutdown_ph();
   extern virtual task cleanup_ph();
   extern virtual function void report_ph();
XCT_IMPL_END

endclass: SE


function SE::new (string name = "", 
                  string inst = "",
                  vmm_consensus end_test,
		              SE_cfg cfg = null);
   
   super.new(name,inst,end_test);
   if(cfg ==null) cfg = new();
	this.cfg = cfg;

endfunction: new
XCT_EXPL_START


function void SE::configured();
   super.configured();
   
   // ToDo: Configure sub env and portion of associated DUT if any
endfunction: configured
NORMAL_START


task SE::start();
   super.start();

   // ToDo: Start the xactors in SE
endtask: start


task SE::stop();
   super.stop();

   // ToDo: Stop the xactors in SE
endtask: stop
NORMAL_END
MACRO_START


task SE::do_start();

   // ToDo: Start the xactors in SE
endtask: do_start


task SE::do_stop();

   // ToDo: Stop the xactors in SE
endtask: do_stop
MACRO_END


task SE::cleanup();
   super.cleanup();
   
   // ToDo: Verify end-of-test conditions
endtask: cleanup


function void SE::report();
   super.report();
   
   // ToDo: Report status or coverage information
endfunction: report
XCT_EXPL_END
XCT_IMPL_START


task SE::config_dut_ph();
   super.config_dut_ph();
   // ToDo: Configure sub env and portion of associated DUT if any

endtask: config_dut_ph


task SE::start_ph();
   super.start_ph();
   // ToDo: Start the Xactors if any
endtask: start_ph


task SE::shutdown_ph();
   super.shutdown_ph();
   // ToDo: Stop the Xactors if any
endtask: shutdown_ph


task SE::cleanup_ph();
   super.cleanup_ph();
endtask: cleanup_ph

function void SE::report_ph();
endfunction: report_ph
XCT_IMPL_END

`endif // SE__SV
