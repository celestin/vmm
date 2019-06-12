//
// Template for VMM-compliant Sub-Environment
// <SE>            Name of Sub-environmnet class
//

`ifndef SE__SV
`define SE__SV


class SE_cfg;

   // ToDo: Add properties for configuring SE

endclass: SE_cfg


class SE extends vmm_subenv;

   SE_cfg      cfg;

   // ToDo: add sub environmnet properties here

MACRO_START
   `vmm_subenv_member_begin(SE)

      // ToDo: add properties using macros here

   `vmm_subenv_member_end(SE)

    // ToDo: Add required short hand override method
MACRO_END

   extern function new(string name = "",
                       string inst = "", 
                       vmm_consensus end_test,
                       SE_cfg cfg = null);
   extern task config_se();
   
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

endclass: SE


function SE::new (string name = "", 
                  string inst = "",
                  vmm_consensus end_test,
                  SE_cfg cfg = null);
   
   super.new(name,inst,end_test);
   cfg=new();
   this.cfg = cfg;

endfunction: new


task SE::config_se();
   // ToDo: Configure sub env and portion of associated DUT if any

   super.configured();
   
endtask: config_se


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

`endif // SE__SV
