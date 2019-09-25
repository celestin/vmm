// Class: vmm_simulation
//
// The <vmm_simulation> class extending from <vmm_unit> is a top-level singleton 
// module that manages the end-to-end simulation timelines. It includes pre-test 
// and post-test timelines with predefined pre-test and post-test phases. The 
// predefined pre-test phases are build, configure, and connect. The predefined 
// post-test phase is final.
//
// Example
//|  program tb_top;
//|    class my_test extends vmm_test;
//|      ...
//|    endclass
//|    class my_env extends vmm_group;
//|      ...
//|    endclass
//|
//|    initial begin
//|      my test test1 = new("test1");
//|      my_env env = new("env");
//|      vmm_simulation my_sim;
//|      my_sim = vmm_simulation::get_sim();
//|      ...
//|    end
//|  endprogram



// Function: new
// Constructs a new <vmm_simulation> object

function vmm_simulation::new();
   vmm_group_genconfigph_phase_def    gen_config_ph;

   super.new(get_typename(), "sim",null);

   // Pre-defined pre/post test phases
   this.pre_test  = new("pre_test","pre_test",  this);
   gen_config_ph      = new;
   void'(this.pre_test.insert_phase_internal("gen_config", "build", gen_config_ph));
   void'(this.pre_test.delete_phase("configure_test"));
   void'(this.pre_test.delete_phase("start_of_sim"));
   void'(this.pre_test.delete_phase("reset"));
   void'(this.pre_test.delete_phase("training"));
   void'(this.pre_test.delete_phase("config_dut"));
   void'(this.pre_test.delete_phase("start"));
   void'(this.pre_test.delete_phase("start_of_test"));
   void'(this.pre_test.delete_phase("run_test"));
   void'(this.pre_test.delete_phase("shutdown"));
   void'(this.pre_test.delete_phase("cleanup"));
   void'(this.pre_test.delete_phase("report"));
   void'(this.pre_test.delete_phase("final"));

   this.top_test  = new("top_test","top_test" , this);
   void'(this.top_test.delete_phase("rtl_config"));
   void'(this.top_test.delete_phase("build"));
   void'(this.top_test.delete_phase("configure"));
   void'(this.top_test.delete_phase("connect"));
   void'(this.top_test.delete_phase("final"));

   this.post_test = new("post_test","post_test", this);
   void'(this.post_test.delete_phase("configure_test"));
   void'(this.post_test.delete_phase("rtl_config"));
   void'(this.post_test.delete_phase("build"));
   void'(this.post_test.delete_phase("configure"));
   void'(this.post_test.delete_phase("connect"));
   void'(this.post_test.delete_phase("start_of_sim"));
   void'(this.post_test.delete_phase("reset"));
   void'(this.post_test.delete_phase("training"));
   void'(this.post_test.delete_phase("config_dut"));
   void'(this.post_test.delete_phase("start"));
   void'(this.post_test.delete_phase("start_of_test"));
   void'(this.post_test.delete_phase("run_test"));
   void'(this.post_test.delete_phase("shutdown"));
   void'(this.post_test.delete_phase("cleanup"));
   void'(this.post_test.delete_phase("report"));
endfunction

function vmm_simulation vmm_simulation::get_sim();
   return me;
endfunction

// //////////////////////////////////////////// 
// Function: get_pre_timeline 
// 
// Returns the vmm_simulation singleton. 
// 
//|   program tb_top;
//|      class my_test extends vmm_test;
//|         ...
//|      endclass
//|   
//|      class my_env extends vmm_group;
//|         ...
//|      endclass
//|   
//|      initial begin
//|         my test test1 = new("test1");
//|         my_env env = new("env");
//|         vmm_simulation my_sim;
//|         ...
//|         my_sim = vmm_simulation :: get_sim;
//|         ... 
//|      end
//|   endprogram
function vmm_timeline vmm_simulation::get_pre_timeline();
   return pre_test;
endfunction

// //////////////////////////////////////////// 
// Function: get_top_timeline 
// 
// Returns the top-level test timeline. 
// 
//|   program tb_top;
//|      class my_test extends vmm_test;
//|         ...
//|      endclass
//|   
//|      class my_env extends vmm_group;
//|         ...
//|      endclass
//|   
//|      initial begin
//|         my test test1 = new("test1");
//|         my_env env = new("env");
//|         vmm_timeline my_tl;
//|         ...
//|         my_tl = get_top_timeline;
//|         ... 
//|      end
//|   endprogram
function vmm_timeline vmm_simulation::get_top_timeline();
   return top_test;
endfunction

// //////////////////////////////////////////// 
// Function: get_post_timeline 
// 
// Returns the post-test timeline. 
// 
function vmm_timeline vmm_simulation::get_post_timeline();
   return post_test;
endfunction

// //////////////////////////////////////////// 
// Function: allow_new_phases 
// 
// Enables the addition of user-defined phases in timelines, if allow is true. If the insertion
// of a user-defined phase is attempted, when new phases are not allowed, an error message
// is issued. 
// By default, addition of user-defined phases are not allowed. 
// 
//|   program tb_top;
//|      class my_test extends vmm_test;
//|         ...
//|      endclass
//|      class my_env extends vmm_group;
//|         ...
//|      endclass
//|   
//|      initial begin
//|         my test test1 = new("test1");
//|         my_env env = new("env");
//|         ...
//|         allow_new_phases;
//|         // insert new phases using 
//|         // insert_pre/post_test_phase tasks
//|      end
//|   endprogram
function void vmm_simulation::allow_new_phases(bit allow = 1);
   allow_new_ph = allow;
endfunction

function bit vmm_simulation::is_allowed_new_phases();
  return allow_new_ph;
endfunction

// Run up to a specified pre-test phase
task vmm_simulation::run_pre_test_phase(string name);
   pre_test.run_phase(name);
endtask

// //////////////////////////////////////////// 
// Function: display_phases 
// 
// Displays how various phases in the various timelines will be executed (that is, in sequence
// or in parallel). Should be invoked after the build phase. 
// 
//|   program tb_top;
//|      class my_test extends vmm_test;
//|         virtual function void start_of_sim_ph();
//|            display_phases;
//|         endfunction
//|      endclass
//|   
//|      class my_env extends vmm_group;
//|      endclass
//|   
//|      initial begin
//|         my test test1 = new("test1");
//|         my_env env = new("env");
//|         ...
//|         run_tests;
//|      end
//|   endprogram
function void vmm_simulation::display_phases();
   vmm_timeline timeline_q[$];
   vmm_timeline tmp_tl;
   vmm_object root_obj;
   string tl_name;
   string phase_name;
   vmm_timeline::METHOD_TYPE meth_type;
   vmm_timeline tl;
   int num_roots = vmm_object::get_num_roots();
   for (int i = 0; i< num_roots; i++) begin
      vmm_object my_obj = vmm_object::get_nth_root(i);
      if ($cast(tl, my_obj)) begin
          timeline_q.push_back(tl);
      end
   end
   begin
      `foreach_vmm_object(vmm_timeline, "@%*", null) begin
           timeline_q.push_back(obj);
       end
   end
   foreach (timeline_q[timeline]) begin
      tmp_tl = timeline_q[timeline];
      `vmm_note(log, `vmm_sformatf("Available phases for %s(%s)",tmp_tl.get_object_hiername(), tmp_tl.get_typename()));
      timeline_q[timeline].display_phase_info();
   end       
endfunction

function int vmm_simulation::collect_root_objects();
   int i = 0;
   string tmp;
   vmm_object root = vmm_object::get_nth_root(i++);
   unphased_details = "";
   Xenv_rootsX.delete();
   while (root != null) begin
      vmm_test test_obj;
      vmm_group group_obj;
      vmm_rtl_config rtl_cfg;
      // All root objects, except
      // the vmm_simulation singleton and tests 
      if (root != vmm_simulation::get_sim() &&
          !$cast(test_obj, root)) begin
          if($cast(rtl_cfg, root) ) begin
              if (rtl_cfg.is_implicitly_phased() == 0)  begin
                 unphased_details = {unphased_details, $psprintf("%30s", rtl_cfg.get_object_hiername()), 
                                    ": implicit phasing turned off\n"};
              end else begin

                 Xenv_rootsX.push_back(root);
             end
          end
          else if($cast(group_obj, root) ) begin
              if (group_obj.is_implicitly_phased() == 0)  begin
                 unphased_details = {unphased_details, $psprintf("%30s", group_obj.get_object_hiername()), 
                                    ": implicit phasing turned off\n"};
              end else begin
                 vmm_subenv subenv_obj;
                 int        present_state;
                 present_state = group_obj.get_num_children();
                 if (!$cast(subenv_obj, root)) begin
                    if(present_state > 1) 
                       group_obj.doneWarningChildlessObject = 0; 
                    else begin
                      if(!group_obj.doneWarningChildlessObject && build_phase_over) begin
                         group_obj.doneWarningChildlessObject = 1;
                         `vmm_warning(group_obj.log, 
                                      $psprintf("root component \"%s\" has no child components", 
                                                 group_obj.get_object_hiername()));
                      end //!group_obj.doneWarningChildlessObject
                    end //!present_state
                 end //!$cast(subenv_obj, root)
              end // !(group_obj.is_implicitly_phased()

             Xenv_rootsX.push_back(root);
          end else 
             unphased_details = {unphased_details, $psprintf("%30s", root.get_object_hiername())
                                , ": non vmm_group extension\n"};
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



   // Remember the state of the environment
   if (tests.num() == 1) begin
      void'(tests.first(testname));
      one_tst = tests[testname];
   end

   // get test/s name from commandline
   cmd_line_tst_file = vmm_opts::get_string("test_file", , "test cases specified in file");
   // get filename containing tests name from commandline
   cmd_line_tst_str = vmm_opts::get_string("test", , "Name of testcase to run");
   if (cmd_line_tst_str != "" && cmd_line_tst_str != "ALL_TESTS")
      `vmm_trace(log,{"tests passed to +vmm_test from command line are ", cmd_line_tst_str});

   if (cmd_line_tst_file != "") begin
      string test_q[$];
      test_fp = $fopen(cmd_line_tst_file,"rb");
      if (test_fp == 0) begin
         `vmm_error(log,`vmm_sformatf("cannot open run test file %s: file does not exist",cmd_line_tst_file));
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
         test_q.push_back(testname);
      end
      $fclose(test_fp);
      foreach (test_q[name]) begin        
         testname = test_q[name];
         tst = tests[testname];
         if (tst.has_config_done() && test_q.size() > 1)
            `vmm_warning(log,`vmm_sformatf("test %s : concatenation is not allowed for this test",testname ));
         if (tst.selected == 1)
            `vmm_warning(log,`vmm_sformatf("test %s is already included for run; ignoring the subsequent entry",testname ));
         else begin
            tst.selected = 1'b1;
            selected_tests.push_back(tst);
         end
      end
   end
   else begin
   // If no tests were specified but only one test is known, run it
      if (cmd_line_tst_str == "") begin
         string str;

         // If there was only one user-defined tests, use it
         if (one_tst != null) begin
            tst = one_tst;
            tst.selected = 1'b1;
            selected_tests.push_back(tst);
         end
         // If there is only the default test, use it
         else if (tests.exists("Default") == 1 ||
                     tests.exists("DEFAULT") == 1 ||
                         tests.exists("default") == 1) begin
            if (tests.exists("Default") == 1)
               tst = tests["Default"];
            else if (tests.exists("DEFAULT"))
               tst = tests["DEFAULT"];
            else
               tst = tests["default"];
            tst.selected = 1'b1;
            selected_tests.push_back(tst);
         end
         // Don't known which test to use!
         else begin
            string msg[$];

            if (tests.num() != 0) begin
               msg.push_back("No test was selected at runtime using +vmm_test=<test>.");
               msg.push_back("Available tests are:");
            end
            else
               msg.push_back("No test was registered");

            display_known_tests(msg, 1);
            return;
         end
      end
      else begin
         if (cmd_line_tst_str == "ALL_TESTS") begin
            foreach (tests[name]) begin
               if (tests[name].has_config_done() && tests.num() > 1)
                  `vmm_warning(log,`vmm_sformatf("test %s : concatenation is not allowed for this test",name ));
               tst = tests[name];
               tst.selected = 1'b1;
               selected_tests.push_back(tst);
            end
         end
         else begin
            string my_tmp_str = "";
            string test_q[$];
            for (int i=0; i<cmd_line_tst_str.len(); i++) begin
              string onechar;
			  onechar = `_TO_CAST_TO_STRING(cmd_line_tst_str.getc(i));
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
                  selected_tests.push_back(tst);
               end
               else begin
                  if (tst.has_config_done() && test_q.size() > 1)
                     `vmm_warning(log,`vmm_sformatf("test %s : concatenation is not allowed for this test",testname ));
                  if (tst.selected == 1'b1)
                     `vmm_warning(log,`vmm_sformatf("test %s is already included for run; ignoring the subsequent entry",testname ));
                  else begin
                        tst.selected = 1'b1;
                        selected_tests.push_back(tst);
                  end
               end
            end
         end
      end
   end
endfunction

function void vmm_simulation::register_unit_consensus();
   int num_of_roots = vmm_object::get_num_roots;
   vmm_object root;
   int index = 0;
   while (index < num_of_roots) begin
     root = vmm_object::get_nth_root(index);
     begin
       vmm_group    group_obj;
       vmm_unit     unit_obj;
       if ($cast(unit_obj, root))
         unit_obj.consent("consent by default");
       if ($cast(group_obj, root)) begin
         vmm_test  test_obj;
         `foreach_vmm_object(vmm_unit, "@%*", root) begin
            vmm_unit unit_obj;
            vmm_object parent = obj.get_parent_object();
            if ((parent != null) && ($cast(unit_obj, parent)))
              unit_obj.vote.register_consensus(obj.vote);
            obj.consent("consent by default ");
         end
       end
     end
     index++;
   end
   vmm_consensus::set_register_consensus();
endfunction

task vmm_simulation::execute_pre_test(string name);
   int        idx;
   int        n_env_roots;
   string     phase_name;
   vmm_phase  ph;
   static bit previously_exectued = 0;
   // get all tests to run

   if (!vmm_consensus::is_register_consensus()) begin
      register_unit_consensus();
   end

   if (name != "$") begin
     ph = pre_test.get_phase(name);
     if (ph == null)
       `vmm_fatal(log, 
                  `vmm_sformatf("Nonexistent phase name \"%s\" passed to pre_test.run_phase(). Exiting Simulation",
                  name));
   end

   if (!previously_exectued) begin
      num_of_test = 0;
      previously_exectued = 1;
      get_tests_to_run();

      // set config for selected tests
      foreach (tests[tst_name]) begin
         if (tests[tst_name].selected == 1'b0) 
            continue;
         else begin
            num_of_test = num_of_test + 1;
         end

         void'(tests[tst_name].has_config_done());
      end
   end


   // Collect a list of root objects that will be implicit
   // children to the run-time timeline
   //n_env_roots = collect_root_objects();
   idx = 0;
   foreach (selected_tests[tst_name]) begin
      if ((selected_tests[tst_name].selected == 1'b0) ||
          (test_status[selected_tests[tst_name].get_object_name()]> 1))
         continue;
      if (idx == 0 && num_of_test > 1 && 
          (!test_status[selected_tests[tst_name].get_object_name()]))
         `vmm_note(log, `vmm_sformatf("Pre-test timeline phases rtl_config, build, connect and configure will only be executed for first test \"%s\" and will not be executed for subsequent tests",selected_tests[tst_name].get_object_name()));
      test_status[selected_tests[tst_name].get_object_name()] = 1;
      if (pre_test.get_current_phase_index() == -1) 
         phase_name = pre_test.get_next_phase_name("^");
      else
         phase_name = pre_test.get_next_phase_name(pre_test.get_current_phase_name());
      //@todo should we give any warning here related to invalid phase_names
      while ((phase_name != "$") && (phase_name != pre_test.get_next_phase_name(name))) begin
          n_env_roots = collect_root_objects();
          Xenv_rootsX.push_back(selected_tests[tst_name]);
          if (pre_test.get_phase_method_type(phase_name) != vmm_timeline::FUNCTION) begin
             `vmm_warning(log, `vmm_sformatf("Phase %s must be a function phase in the pre-test",phase_name));
          end
          pre_test_active = 1;
          pre_test.run_phase_internal(phase_name);
          if (phase_name == "build")
              build_phase_over = 1;
          phase_name = pre_test.get_next_phase_name(phase_name);
      end
      if (phase_name == "$") 
        test_status[selected_tests[tst_name].get_object_name()] = 2;
      else
        break;
      idx++;
   end
  // check if there is any vmm_env instance
   if (phase_name == "$") begin
      foreach (Xenv_rootsX[p]) begin
         vmm_env e;
         vmm_object r;
         r = Xenv_rootsX[p];
         if ($cast(e, r)) begin
            `vmm_warning(log, "vmm_env is instantiated in an implicitly phased environment");      continue;
         end
      end

      foreach (selected_tests[tst_name]) begin
         vmm_unit u;
         for (int i=0; i<selected_tests[tst_name].get_num_children(); i++) begin
            if ($cast(u, selected_tests[tst_name].get_nth_child(i)))
               `vmm_warning(log, `vmm_sformatf("vmm_test %s: Structural components like Transactor and Environment should not be instantiated in vmm_test",selected_tests[tst_name].get_object_name()));
         end
      end

      if (vmm_opts::get_bit("list_phases", "Lists all the available phases for the simulation")) begin
         string phase_list = "Available phases in this simulation are as given below\n";
         phase_list = {phase_list, find_phases(pre_test),
                    find_phases(top_test), find_phases(post_test)};
         foreach (Xenv_rootsX[p]) begin
            phase_list = {phase_list, find_phases(Xenv_rootsX[p])};
         end
         `vmm_note(log, phase_list);
      end

      if (vmm_opts::get_bit("list_timeline", "Lists all the timelines present in the simultion")) begin
         string timeline_list = "Available timelines in this simulation are as given below\n";
         timeline_list = {timeline_list, find_timelines(pre_test),
                    find_timelines(top_test), find_timelines(post_test)};
         foreach (Xenv_rootsX[p]) begin
            timeline_list = {timeline_list, find_timelines(Xenv_rootsX[p])};
         end
         `vmm_note(log, timeline_list);
      end
   end
endtask

task vmm_simulation::execute_top_test(string name);
   int       idx;
   int       n_env_roots;
   string    phase_name;
   vmm_phase ph;
   string    tmp_tst_name = "";
   string    str = "";
   idx = 0;

   if (name != "$") begin
     ph = top_test.get_phase(name);
     if (ph == null)
       `vmm_fatal(log, 
                  `vmm_sformatf("Nonexistent phase name \"%s\" passed to top_test.run_phase(). Exiting Simulation",
                  name));
   end

   if (pre_test.get_next_phase_name(pre_test.get_current_phase_name()) != "$") begin
      execute_pre_test("$");
   end
   foreach (selected_tests[tst_name]) begin
      string str_tmp;
      if ((selected_tests[tst_name].selected == 1'b0) ||
          (test_status[selected_tests[tst_name].get_object_name()] == 4)) 
         continue;

      // if a test is selected, add it to the run-time roots
      if (test_status[selected_tests[tst_name].get_object_name()] == 2)
        `vmm_note(log, {"Running Test Case ", selected_tests[tst_name].get_object_name()});
      //Xenv_rootsX.push_back(selected_tests[tst_name]);

      test_status[selected_tests[tst_name].get_object_name()] = 3;



      if (idx > 0) begin
         // Reset the environment, including random seeds
         // to the state marked before running tests
         //Xenv_rootsX = Xenv_rootsX[0:n_env_roots-1];
         selected_tests[tst_name].concatenate_test_n_reset_phase();
         if (selected_tests[tst_name].XresetToPhaseX == "rtl_config" ||
             selected_tests[tst_name].XresetToPhaseX == "build"      ||
             selected_tests[tst_name].XresetToPhaseX == "configure"  ||
             selected_tests[tst_name].XresetToPhaseX == "connect" ) begin
             `vmm_warning(log, `vmm_sformatf("test %s cannot be rolled back to pre_test phase(%s); test will not run", selected_tests[tst_name].get_object_name(), selected_tests[tst_name].XresetToPhaseX));
             continue;
         end
         if (selected_tests[tst_name].XresetToPhaseX != "^") begin
            top_test.configure_test_ph();
         end
         top_test.reset_to_phase(selected_tests[tst_name].XresetToPhaseX);
         log.reset_message_count(vmm_log::ERROR_SEV, "/./", "/./");
         log.reset_message_count(vmm_log::WARNING_SEV, "/./", "/./");
      end

       if (top_test.get_current_phase_index() == -1) 
          phase_name = top_test.get_next_phase_name("^");
       else
          phase_name = top_test.get_next_phase_name(top_test.get_current_phase_name());
      while((phase_name != "$") && (phase_name != top_test.get_next_phase_name(name))) begin
          n_env_roots = collect_root_objects();
          Xenv_rootsX = Xenv_rootsX[0:n_env_roots-1];
          Xenv_rootsX.push_back(selected_tests[tst_name]);
          if (phase_name == "reset") begin
             if (vmm_opts::get_bit("help", "Displays a list of all VMM options that can be queried during run-time"))
                vmm_opts::get_help();
          end
          top_test_active = 1;
          top_test.run_phase_internal(phase_name);
          if (unphased_details != "")
            str_tmp = {str_tmp, "For phase \"", phase_name, "\"\n", unphased_details};
          phase_name = top_test.get_next_phase_name(phase_name);
      end
      tmp_tst_name  = selected_tests[tst_name].get_object_name();
      if (phase_name == "$") begin
         test_status[selected_tests[tst_name].get_object_name()] = 4;
         `vmm_note(log, {"Test Case ", tmp_tst_name, " Done"});
      end else begin
        break;
      end
      errors[tmp_tst_name] = log.get_message_count(vmm_log::ERROR_SEV, "/./", "/./");
      warns[tmp_tst_name] = log.get_message_count(vmm_log::WARNING_SEV, "/./", "/./");
      if (width < tmp_tst_name.len()) width = tmp_tst_name.len();
      idx++;

      if(str_tmp != "") 
        str = {str, "Unphased components during the execution of test \"", selected_tests[tst_name].get_object_name(), "\"\n", str_tmp};
   end // foreach selected_tests[tst_name]
endtask

task vmm_simulation::execute_post_test(string name);
   string    phase_name;
   int       n_env_roots;
   vmm_phase ph;
   string    str = "";
   string    tmp_tst_name = "";
   string    d_str = "";
   int       t_width = 0;

   if (name != "$") begin
     ph = post_test.get_phase(name);
     if (ph == null)
       `vmm_fatal(log, 
                  `vmm_sformatf("Nonexistent phase name \"%s\" passed to post_test.run_phase(). Exiting Simulation",
                  name));
   end


   if (top_test.get_next_phase_name(top_test.get_current_phase_name()) != "$") begin
      execute_top_test("$");
   end

   if (post_test.get_current_phase_index() == -1) 
      phase_name = post_test.get_next_phase_name("^");
   else
      phase_name = post_test.get_next_phase_name(post_test.get_current_phase_name());
   while ((phase_name != "$") && (phase_name != post_test.get_next_phase_name(name))) begin
       n_env_roots = collect_root_objects();
       Xenv_rootsX = Xenv_rootsX[0:n_env_roots-1];
       post_test_active = 1;
       post_test.run_phase_internal(phase_name);
       phase_name = post_test.get_next_phase_name(phase_name);
   end
   if (num_of_test > 1) begin
      string status_str, spaces;
      int errs, wrns, spc_cnt;
      spaces = {width {" "}};
      d_str = {54+width {"-"}};
      $display("|%s|",d_str);
      $display("|\tS U M M A R Y   O F    A L L   T E S T S");
      $display("|%s|",d_str);
      foreach (errors[tst_name]) begin
         if (errors[tst_name] == 0) status_str = "PASSED";
         else status_str = "FAILED";
         errs += errors[tst_name];
         wrns += warns[tst_name];
         tmp_tst_name = tst_name;
         t_width = tmp_tst_name.len();
         spc_cnt = spaces.len() - t_width;
         $display("\t%s%s : %s (%0d Errors, %0d Warnings)", tst_name, spaces.substr(0, spc_cnt), status_str, errors[tst_name], warns[tst_name]);
      end
      $display("|%s|",d_str);
      $display("|\tTOTAL = %0d Errors, %0d Warnings", errs, wrns);
      $display("|%s|",d_str);
   end
   if (str == "") 
      str = "All root components were phased during this simulation\n";
   else begin 
      str = {"|----------------------------------------------------------------|\n", str};
      str = {"|\tL I S T   O F   I M P L I C I T L Y  U N P H A S E D  R O O T  C O M P O N E N T S\n", str};
      str = {"|----------------------------------------------------------------|\n", str};
   end
   `vmm_debug(log, str);
endtask

task vmm_simulation::run_tests();
   execute_pre_test("$");
   execute_top_test("$");
   execute_post_test("$");
endtask

function void vmm_simulation::Xregister_testX(vmm_test tst);
   string name;

   if (tst == null) begin
      `vmm_error(log, "Attempting to register NULL test.");
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

  if (tests.num() != 0) msg.push_back("Available tests are:");
  msg.push_back(str);
  display_known_tests(msg, 0);
endfunction

function void vmm_simulation::display_known_tests(ref string msg[$],
                                                  input bit fatal);
   bit [12:0] n = 0;
   string     str;
   static string spaces = "                                            ";

   n = 1;
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

function string vmm_simulation::find_timelines(vmm_object obj);
  vmm_timeline tl;

  find_timelines = "";
  if ($cast(tl, obj)) 
    find_timelines = {tl.get_object_hiername(), "\n"};

  for (int index = 0; index < obj.get_num_children(); index ++) begin
     find_timelines = {find_timelines, find_timelines(obj.get_nth_child(index))};
  end

  return find_timelines;
endfunction

function string vmm_simulation::find_phases(vmm_object obj);
  vmm_timeline tl;
  find_phases = "";
  if ($cast(tl, obj)) begin
    string next_phase_name = "^";
    next_phase_name = tl.get_next_phase_name(next_phase_name);
    find_phases = {"Phases in Timeline \"", tl.get_object_hiername(), "\":"};
    while (next_phase_name != "$") begin
      find_phases = {find_phases, " ", next_phase_name};
      next_phase_name = tl.get_next_phase_name(next_phase_name);
    end
    find_phases = {find_phases, "\n"};
  end

  for (int index =0; index < obj.get_num_children(); index ++) begin
    find_phases = {find_phases, find_phases(obj.get_nth_child(index))};
  end
endfunction

function string vmm_simulation::get_current_phase_name();
   if (pre_test_active && post_test_active && top_test_active)
     return "$";
   if (post_test_active) 
      return post_test.get_current_phase_name();
   else if (top_test_active)
      return top_test.get_current_phase_name();
   else if (pre_test_active)
      return pre_test.get_current_phase_name();
   else
      return "^";
endfunction

`ifdef VMM_SV_SC_INTEROP
function void vmm_simulation::set_sv2sc_interop();
   vmm_timeline                post_timeline;
   vmm_timeline                top_timeline;
   
   post_timeline = vmm_simulation::get_post_timeline();
   top_timeline = vmm_simulation::get_top_timeline();
   
   top_timeline.set_sv2sc_interop();
   post_timeline.set_sv2sc_interop();
endfunction:set_sv2sc_interop

function void vmm_simulation::set_sc2sv_interop();
   vmm_timeline                post_timeline;
   vmm_timeline                top_timeline;
   
   post_timeline = vmm_simulation::get_post_timeline();
   top_timeline = vmm_simulation::get_top_timeline();
   
   top_timeline.set_sc2sv_interop();
   post_timeline.set_sc2sv_interop();
endfunction:set_sc2sv_interop
`endif
