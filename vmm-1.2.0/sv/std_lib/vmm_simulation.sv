/*********************************************************************
 *    Copyright 2004-2009 Synopsys, Inc.
 *    All Rights Reserved Worldwide
 *
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

function vmm_simulation::new();
   super.new(get_type(), "sim",null);

   // Pre-defined pre/post test phases
   this.pre_test  = new("pre_test","pre_test",  this);
   this.pre_test.delete_phase("start_of_sim");
   this.pre_test.delete_phase("reset");
   this.pre_test.delete_phase("training");
   this.pre_test.delete_phase("config_dut");
   this.pre_test.delete_phase("start");
   this.pre_test.delete_phase("start_of_test");
   this.pre_test.delete_phase("run_test");
   this.pre_test.delete_phase("shutdown");
   this.pre_test.delete_phase("cleanup");
   this.pre_test.delete_phase("report");
   this.pre_test.delete_phase("destruct");

   this.top_test  = new("top_test","top_test" , this);
   this.top_test.delete_phase("rtl_config");
   this.top_test.delete_phase("build");
   this.top_test.delete_phase("configure");
   this.top_test.delete_phase("connect");

   this.post_test = new("post_test","post_test", this);
   this.post_test.delete_phase("rtl_config");
   this.post_test.delete_phase("build");
   this.post_test.delete_phase("configure");
   this.post_test.delete_phase("connect");
   this.post_test.delete_phase("start_of_sim");
   this.post_test.delete_phase("reset");
   this.post_test.delete_phase("training");
   this.post_test.delete_phase("config_dut");
   this.post_test.delete_phase("start");
   this.post_test.delete_phase("start_of_test");
   this.post_test.delete_phase("run_test");
   this.post_test.delete_phase("shutdown");
   this.post_test.delete_phase("cleanup");
   this.post_test.delete_phase("destruct");
endfunction

function vmm_simulation vmm_simulation::get_sim();
   return me;
endfunction

function vmm_timeline vmm_simulation::get_pre_timeline();
   return pre_test;
endfunction

function vmm_timeline vmm_simulation::get_top_timeline();
   return top_test;
endfunction

function vmm_timeline vmm_simulation::get_post_timeline();
   return post_test;
endfunction

function bit vmm_simulation::insert_test_phase(string phase_name,
                                               string before_name,
                                               vmm_phase_def def);
   if (allow_new_ph)
      return top_test.insert_phase(phase_name, before_name, def);
   else begin
      `vmm_error(log,`vmm_sformatf("New phases are not allowed"));
      `vmm_error(log,`vmm_sformatf("call allow_new_phases() before inserting new phase"));
   end
endfunction

function void vmm_simulation::allow_new_phases(bit allow = 1);
   allow_new_ph = allow;
endfunction

// Run up to a specified pre-test phase
task vmm_simulation::run_pre_test_phase(string name);
   pre_test.run_phase(name);
endtask

function void vmm_simulation::display_phases();
   vmm_timeline timeline_q[$];
   vmm_timeline tmp_tl;
   string map [string];
   vmm_object root_obj;
   string tl_name;
   string phase_name;
   vmm_timeline::METHOD_TYPE meth_type;
   foreach (Xenv_rootsX[root]) begin
      root_obj = Xenv_rootsX[root];
      if ($cast(tmp_tl, root_obj) == 1) begin
         timeline_q.push_back(tmp_tl);
         begin
            `foreach_vmm_object(vmm_timeline, "@%*", root_obj) begin
                 timeline_q.push_back(obj);
             end
         end
      end
   end
   foreach (timeline_q[timeline]) begin
      tmp_tl = timeline_q[timeline];
      $display("    Available phases for %s(%s)", tmp_tl.get_hier_inst_name(), tmp_tl.get_typename());
      tl_name = tmp_tl.get_object_name();
      phase_name = tmp_tl.get_next_phase_name("^");
      while (phase_name != "$" && phase_name != "?") begin
         string tmp_tl_name;
         if (map.exists(phase_name)) begin
            tmp_tl_name = map[phase_name];
            map[phase_name] = {tmp_tl_name, "| ",tl_name};
         end
         else begin
            map[phase_name] = {": ", tl_name};
         end
         $display("\t%30s %30s", phase_name, map[phase_name]);
         phase_name = tmp_tl.get_next_phase_name(phase_name);
      end
   end
endfunction

function int vmm_simulation::collect_root_objects();
   int i = 0;
   vmm_object root = vmm_object::get_nth_root(i++);
   Xenv_rootsX.delete();
   while (root != null) begin
      vmm_test test_obj;
      // All root objects, except
      // the vmm_simulation singleton and tests 
      if (root != vmm_simulation::get_sim() &&
          !$cast(test_obj, root) ) begin
         Xenv_rootsX.push_back(root);
      end
      root = vmm_object::get_nth_root(i++);
   end
   return Xenv_rootsX.size();
endfunction

function void vmm_simulation::get_tests_to_run();
   int test_fp;
   string   testname;
   string   cmd_line_tst_str;
   string   cmd_line_tst_file;
   vmm_test tst = null;
   vmm_test one_tst = null;


   //vmm_object::print_object_hierarchy();

   // Remember the state of the environment
   if (tests.num() == 1) begin
      void'(tests.first(testname));
      one_tst = tests[testname];
   end

   if (!tests.exists("Default")) begin
      // Create a default testcase and run it
      tst = new("Default", "Default testcase that simply calls env::run()");
   end

   // get test/s name from commandline
   cmd_line_tst_file = vmm_opts::get_string("test_file", , "test cases specified in file");
   // get filename containing tests name from commandline
   cmd_line_tst_str = vmm_opts::get_string("test", , "Name of testcase to run");
   if (cmd_line_tst_str != "" && cmd_line_tst_str != "ALL_TESTS")
      `vmm_note(log,{"test name is ", cmd_line_tst_str});

   if (cmd_line_tst_file != "") begin
      test_fp = $fopen(cmd_line_tst_file,"rb");
      if (test_fp == 0) begin
         `vmm_error(log,`vmm_sformatf("can not open run test file %s: file does not exist",cmd_line_tst_file));
         return;
      end
      if ($feof(test_fp)) begin
         `vmm_error(log,`vmm_sformatf("run test file %s is empty",cmd_line_tst_file));
         return;
      end
      while($fscanf(test_fp, "%s", testname) == 1) begin
         if (!tests.exists(testname)) begin
            string msg[$];
            string str;

            $sformat(str, "Unknown test name \"%s\" specified.", testname);
            msg.push_back(str);
            display_known_tests(msg, 1);
            return;
         end
         tst = tests[testname];
         if (tst.has_config_done())
            `vmm_warning(log,`vmm_sformatf("test %s will not run as concatenation is not allowed for this test",testname ));
         else
            tst.selected = 1'b1;
      end
      $fclose(test_fp);
   end
   else begin
   // If no tests were specified but only one test is known, run it
      if (cmd_line_tst_str == "") begin
         string str;

         // If there was only one user-defined tests, use it
         if (one_tst != null) begin
            tst = one_tst;
            tst.selected = 1'b1;
         end
         // If there is only the default test, use it
         else if (tests.num() == 1) begin
            void'(tests.first(testname));
            tst = tests[testname];
            tst.selected = 1'b1;
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
         if (cmd_line_tst_str == "ALL_TESTS") begin
            foreach (tests[name])
               if (tests[name].has_config_done())
                  `vmm_warning(log,`vmm_sformatf("test %s will not run as concatenation is not allowed for this test",name ));
               else
                  tests[name].selected = 1'b1;
         end
         else begin
            string my_tmp_str = "";
            string test_q[$];
            for (int i=0; i<cmd_line_tst_str.len(); i++) begin
              string onechar = cmd_line_tst_str.getc(i);
              if (onechar == "+") begin
                 test_q.push_back(my_tmp_str);
                 my_tmp_str = "";
                 continue;
              end
              my_tmp_str = {my_tmp_str, onechar};
            end
            test_q.push_back(my_tmp_str);
            foreach (test_q[name]) begin        
               testname = test_q[name];
               if (!tests.exists(testname)) begin
                  string msg[$];
                  string str;
 
                  $sformat(str, "Unknown test name \"%s\" specified.", testname);
                  msg.push_back(str);
                  display_known_tests(msg, 1);
                  return;
               end
               tst = tests[testname];
               if (test_q.size() == 1) begin
                  tst.selected = 1'b1;
               end
               else begin
                  if (tst.has_config_done())
                     `vmm_warning(log,`vmm_sformatf("test %s will not run as contatination is not allowed for this test",testname ));
                  else
                     tst.selected = 1'b1;
               end
            end
         end
      end
   end
endfunction

task vmm_simulation::run_tests();
   int n_env_roots;
   int idx;

   // get all tests to run
   get_tests_to_run();

   // set config for selected tests
   foreach (tests[tst_name]) begin
      if (tests[tst_name].selected == 1'b0) 
         continue;

      void'(tests[tst_name].has_config_done());
   end

   // Collect a list of root objects that will be implicit
   // children to the run-time timeline
   n_env_roots = collect_root_objects();

   pre_test.run_phase("$");

   idx = 0;
   foreach (tests[tst_name]) begin
      if (tests[tst_name].selected == 1'b0) 
         continue;

      if (idx > 0) begin
         // Reset the environment, including random seeds
         // to the state marked before running tests
         Xenv_rootsX = Xenv_rootsX[0:n_env_roots-1];
         top_test.reset_to_phase("start_of_sim");
      end

      // if a test is selected, add it to the run-time roots
      `vmm_note(log, {"Running Test Case ", tst_name});
      Xenv_rootsX.push_back(tests[tst_name]);

      top_test.run_phase("$");
      `vmm_note(log, {"Test Case ", tst_name, " Done"});
      idx++;
   end

   Xenv_rootsX = Xenv_rootsX[0:n_env_roots-1];
   post_test.run_phase("$");
   log.report();
endtask

function void vmm_simulation::Xregister_testX(vmm_test tst);
   string name;

   if (tst == null) begin
      `vmm_error(log, "Attemtping to register NULL test.");
      return;
   end

   name = tst.get_name();
   if (tests.exists(name)) begin
      `vmm_error(log, `vmm_sformatf("Attempting to register test \"%s\" more than once.",
                                     name));
      return;
   end

   tests[name] = tst;

   if (name.len() > width) width = name.len();
endfunction

function void vmm_simulation::list();
  string msg[$];
  string str;

  msg.push_back("Available tests are:");
  msg.push_back(str);
  display_known_tests(msg, 0);
endfunction

function void vmm_simulation::display_known_tests(ref string msg[$],
                                                  input bit fatal);
   bit [12:0] n = 0;
   string     str;
   static string spaces = "                                            ";

   foreach (tests[name]) begin
      string testname = name;
      $sformat(str, "%d) %s%s : %s", n++, testname,
               spaces.substr(0, width-testname.len()-1),
               tests[name].get_doc());
      msg.push_back(str);
   end
   if ((fatal && log.start_msg(vmm_log::FAILURE_TYP, vmm_log::FATAL_SEV)) ||
       (!fatal && log.start_msg(vmm_log::NOTE_TYP, vmm_log::NORMAL_SEV))) begin
      foreach (msg[i]) void'(log.text(msg[i]));
      log.end_msg();
   end
endfunction
