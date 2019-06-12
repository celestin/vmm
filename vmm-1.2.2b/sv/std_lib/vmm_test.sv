// //////////////////////////////////////////// 
// Class: vmm_test_registry
//
// Global test registry that can be optionally used to implement runtime selection of 
// tests. No constructor is documented, because this class is implemented using a 
// singleton pattern.
//
// Its functionality is accessed strictly through static members.
  
function void vmm_test_registry::Xregister_testX(vmm_test tst);
   string name;

   if (tst == null) begin
      `vmm_error(log, "Attemtping to register NULL test.");
      return;
   end

   name = tst.get_name();

   if (registry.exists(name)) begin
      `vmm_error(log, `vmm_sformatf("Attempting to register test \"%s\" more than once.",
                                    name));
      return;
   end

   registry[name] = tst;

   if (name.len() > width) width = name.len();
endfunction


// Task: run
//
// Runs a testcase on the specified verification environment. 
// This method must be invoked in a program thread to satisfy 
// Verification Methodology Manual rules.
//
// If more than one testcase is registered, then the name of a testcase must be 
// specified using the "+vmm_test" runtime string option. For more information, 
// see the section, <vmm_opts::get_string> to know how to specify runtime string 
// options. 
//
// If only one test is registered, then it is run by default without having to specify 
// its name at runtime. A default testcase, named "Default" that simply invokes 
// <run>, is automatically available if no testcase is previously registered under that name.
  
task vmm_test_registry::run(vmm_env env);
   string   testname;
   vmm_test tst = null;
   vmm_test one_tst = null;
  
   if (registry.num() == 1) begin
      void'(registry.first(testname));
      one_tst = registry[testname];
   end

   if (!registry.exists("Default")) begin
      // Create a default testcase and run it
      tst = new("Default", "Default testcase that simply calls env::run()");
   end

   if (_vmm_opts.get_bit("test_help", "List available testcases")) begin
      list();
      $finish();
   end

   testname = _vmm_opts.get_string("test", ,
                                   "Name of testcase to run");

   // If no tests were specified but only one test is known, run it
   if (testname == "") begin
      string str;

      // If there was only one user-defined tests, use it
      if (one_tst != null) begin
         tst = one_tst;
         testname = tst.get_name();
      end
      // If there is only the default test, use it
      else if (registry.num() == 1) begin
         void'(registry.first(testname));
         tst = registry[testname];
      end
      // Don't known which test to use!
      else begin
         string msg[$];

         msg.push_back("No test was selected at runtime using +vmm_test=<test>.");
         msg.push_back("Available tests are:");
         display_known_tests(msg, 1);
         return;
      end
   end
   else begin
      if (!registry.exists(testname)) begin
         string msg[$];
         string str;

         $sformat(str, "Unknown test name \"%s\" specified.", testname);
         msg.push_back(str);
         display_known_tests(msg, 1);
         return;
      end
      tst = registry[testname];
   end

   `vmm_note(log, `vmm_sformatf("Running test \"%s\"...", testname));
   tst.run(env);
endtask


// //////////////////////////////////////////// 
// Function: list 
// 
// Lists the tests that are registered with the global test registry. 
// This method is invoked automatically by the <run() method, followed
// by a call to $finish>, if the +vmm_test_help option is specified. 
// 
//|   
//|   program test;
//|      `include "test.lst"
//|      i2c_env env;
//|   
//|      initial begin
//|         vmm_test_registry registry = new;
//|         env = new;
//|         registry.list();
//|         registry.run(env);
//|      end
//|   endprogram
function void vmm_test_registry::list();
   string msg[$];
   string str;

   msg.push_back("Available tests are:");
   msg.push_back(str);
   display_known_tests(msg, 0);
endfunction


function void vmm_test_registry::display_known_tests(ref string msg[$],
                                                     input bit fatal);
   bit [12:0] n = 0;
   string     str;
   static string spaces = "                                            ";

   n = 0;
   foreach (registry[name]) begin
      string testname = name;
      $sformat(str, "%d) %s%s : %s", n++, testname,
               spaces.substr(0, width-testname.len()-1),
               registry[name].get_doc());
      msg.push_back(str);
   end
   if ((fatal && log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) ||
       (!fatal && log.start_msg(vmm_log::NOTE_TYP, vmm_log::NORMAL_SEV))) begin
      foreach (msg[i]) void'(log.text(msg[i]));
      log.end_msg();
   end
endfunction

// //////////////////////////////////////////// 
// Class: vmm_test
//
// The vmm_test class is an extension of vmm_timeline, and handles the test 
// execution timeline with all of the default predefined phases. This is used 
// as the base class for all tests.
//
// Instances of this class must be either root objects or children of vmm_test objects.
//
// Example
//|   class my_test1 extends vmm_test;
//|     `vmm_typename(my_test1)
//|     function new(string name);
//|       super.new(name);
//|     endfunction
//|     function void config_ph;
//|       cfg cfg1 = new;
//|       if (cfg1.randomize)
//|         `vmm_note (log, "CFG randomized successfully" );
//|       else
//|         `vmm_error (log, "CFG randomization failed" );
//|     endfunction
//|   endclass

function void vmm_test::concatenate_test_n_reset_phase();
endfunction:concatenate_test_n_reset_phase

// //////////////////////////////////////////// 
// Function: new 
// 
// Creates an instance of the testcase, its message service interface, and registers
// it in the global testcase registry under the specified name. A short description of
// the testcase may also be specified. 
// 
//|   
//|   class my_test extends vmm_test;
//|      function new();
//|         super.new("my_test");
//|      endfunction
//|      static my_test this_test = new();
//|      virtual task run(vmm_env env);
//|         ...
//|      endtask
//|   endclass
function vmm_test::new(string name = "", string doc = "", vmm_object parent = null);
`ifdef VMM_TEST_BASE
      super.new(get_typename(),name, parent);
`endif
   begin
      this.log = new("Testcase", name);
      this.doc = doc;
      this.registry.Xregister_testX(this);
      `ifndef NO_VMM12_PHASING
      vmm_simulation::Xregister_testX(this);
      `endif
   end
endfunction

function void vmm_test::set_config();
   config_enable = 1;
endfunction

// //////////////////////////////////////////// 
// Function: get_doc 
// 
// Returns the short description of the test that was specified in the constructor. 
// 
//|   
//|   class my_test extends vmm_test;
//|      function new();
//|         super.new("my_test");
//|      endfunction
//|      static my_test this_test = new();
//|      virtual task run(vmm_env env);
//|         vmm_note(this.log, 
//|            {"Running test ", this.get_doc()});
//|         ...
//|      endtask
//|   endclass
function string vmm_test::get_doc();
   return this.doc;
endfunction

// //////////////////////////////////////////// 
// Function: get_name 
// 
// Returns the name of the test that was specified in the constructor. 
// 
//|   
//|   class my_test extends vmm_test;
//|      function new();
//|         super.new("my_test");
//|      endfunction
//|      static my_test this_test = new();
//|      virtual task run(vmm_env env);
//|         vmm_note(this.log,
//|            {"Running test ", this.get_name()});
//|         ...
//|      endtask
//|   endclass
function string vmm_test::get_name();
   return this.log.get_instance();
endfunction

function bit vmm_test::has_config_done();
   if (!config_called) set_config();
   config_called = 1;
   return ~config_enable;
endfunction

function void vmm_test::report_ph();
   log.report();
endfunction

function void vmm_test::Xset_log_instanceX(string inst);
   this.log.set_instance(inst);
endfunction

task vmm_test::run(vmm_env env);
   env.run();
endtask


