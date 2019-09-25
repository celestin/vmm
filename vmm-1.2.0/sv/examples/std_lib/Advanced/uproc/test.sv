/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

`include "common_instruction_scenario.sv"

class basic_instruction_scenario extends common_instruction_scenario;
  integer BASIC;
  bit back_branch = 1;
  
  constraint length_repeated_valid {
    if (scenario_kind == BASIC) {
      repeated == 0;
      length == 20;
    }
  }

  constraint no_sb {
    foreach (items[i]) {
      !(items[i].op[0].kind inside { opcode::SB });
    }
  }
    
  constraint few_nop {
    foreach (items[i]) {
      items[i].op[0].opcode_type dist { opcode::NO_OPERATION := 1, [opcode::LOAD_STORE:opcode::LABEL_NAME] := 9 };
      items[i].op[1].opcode_type dist { opcode::NO_OPERATION := 1, [opcode::LOAD_STORE:opcode::LABEL_NAME] := 9 };			
    }
  }
								
  constraint single_branch {
    foreach (items[i]) {
      if (back_branch == 0) {
        if (i == 2) {
          items[i].op[0].opcode_type == opcode::CONTROL;
          items[i].op[1].opcode_type != opcode::CONTROL;
        }
        if (i != 2) {
          items[i].op[0].opcode_type != opcode::CONTROL;
          items[i].op[1].opcode_type != opcode::CONTROL;
        }
      }
      if (back_branch == 1) {
        if (i == 18) {
          items[i].op[0].opcode_type == opcode::CONTROL;
          items[i].op[1].opcode_type != opcode::CONTROL;
        }
        if (i != 18) {
          items[i].op[0].opcode_type != opcode::CONTROL;
          items[i].op[1].opcode_type != opcode::CONTROL;
        }
      }
    }
  }
  

  function void pre_randomize();
    super.pre_randomize();
    back_branch = $random()%2;
     
`ifdef DEBUG
    $display ("back_branch = %0d\n", back_branch);
    $display ("op_branch_labels.list.size() = 'd%0d\n", op_branch_labels.list.size());
    op_branch_labels.display();
`endif
     
  endfunction // void
   
  
   function new();
    super.new();
    op_branch_labels = new (1, 4, 16);
    this.BASIC = define_scenario("BASIC", 20);
   endfunction // new
   
   function vmm_data allocate();
      basic_instruction_scenario scn = new;
      allocate = scn;
   endfunction

   function vmm_data copy(vmm_data to = null);
      basic_instruction_scenario scn = new;
      scn.BASIC = this.BASIC;
      scn.back_branch = this.back_branch;
      scn.stream_id = this.stream_id;
      scn.scenario_id = this.scenario_id;
      copy = scn;
   endfunction

`vmm_class_factory(basic_instruction_scenario)

endclass // basic_instruction_scenario


class env extends vmm_unit;
`vmm_typename(env)
  instruction_scenario_gen gen;
  common_instruction_scenario scn;

   function new(string name);
     super.new(get_typename(), name);
   endfunction

   virtual function void build_ph();
      gen = new ("instruction", 0);
      scn = new();
      // unregistering the existing Atomic scenario and register the new one
      void'(gen.unregister_scenario_by_name("Atomic"));
      gen.register_scenario("common_scenario", scn);
   endfunction

   virtual task start_ph();
      gen.start_xactor();
   endtask
endclass


class test extends vmm_test;
  `vmm_typename(test)
    
  env my_env;

  function new(string name, env my_env);
     super.new(name);
     this.my_env = my_env;
  endfunction

  virtual function void start_of_sim_ph();
     // Sneak in new factory :
     // generator and scenario name (in case of scenario gen) have to be provided
     common_instruction_scenario::override_with_new("@%env1:instruction:common_scenario", 
                                basic_instruction_scenario::this_type, log);
      fork
	 while (1) begin
	    string prefix;
	    instruction t = new;
	    my_env.gen.out_chan.get(t);
	    $sformat (prefix, "[%2d.%2d.%2d] ",
		      t.stream_id, t.scenario_id, t.data_id);
	    $display ("%0s", t.psdisplay(prefix));
	 end
      join_none
      my_env.gen.stop_after_n_scenarios = 5;
  endfunction

  virtual task shutdown_ph();
    my_env.gen.notify.wait_for (instruction_scenario_gen::DONE);
  endtask

endclass


program automatic P;

test t1;

initial begin
      env my_env = new("env1");
      t1 = new("test1", my_env);
      vmm_simulation::run_tests();
end
endprogram

