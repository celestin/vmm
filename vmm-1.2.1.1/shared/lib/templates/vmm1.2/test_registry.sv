//
// Template for VMM-compliant Program block
// <PB>        Name of the Program block
// <ENV>       Name of Environment 
// <IF>        Name of Physical interface
// <PRT>       Name of Interface wrapper class
//

`ifndef PB__SV
`define PB__SV

`include "IF.sv"

SING_DRV_START
program PB(IF intf);
SING_DRV_END
MULT_DRV_START
program PB(IF intf [INTF_COUNT]);
MULT_DRV_END

`include "ENV.sv"
`include "TEST_NAME.sv"  //ToDo: Change this name to the testcase file-name
 // ToDo: Include all other test list here

   ENV env;
   SING_DRV_START
   PRT if_port;
   SING_DRV_END
   MULT_DRV_START
   PRT if_port[INTF_COUNT];
   MULT_DRV_END
   MACRO_START
   TST_EXPL_START
   vmm_test_registry registry;
   TST_EXPL_END
   MACRO_END
   RTLCFG_START
   vmm_rtl_config_default_file_format dflt_fmt;
   env_config env_cfg;
   RTLCFG_END
   initial begin
      SING_DRV_START
      if_port = new("if_port",intf);
      vmm_opts::set_object("drv_port", if_port);  
      vmm_opts::set_object("mon_port", if_port);
      GEN_SL_RCVR_START
      vmm_opts::set_object("rec_port", if_port);
      GEN_SL_RCVR_END
      SING_DRV_END
      MULT_DRV_START
      if_port[0] = new("if_port",intf[0]);
      vmm_opts::set_object("drv_port", if_port[0]);
      vmm_opts::set_object("mon_port", if_port[0]);
      //ToDo: For multi interfaces in single env, user need to create and set other if_ports
      GEN_SL_RCVR_START
      vmm_opts::set_object("rec_port", if_port[0]);
      GEN_SL_RCVR_END 
      MULT_DRV_END
      env = new("env");
      RTLCFG_START
      env_cfg = new("env_cfg");
      env.env_cfg = env_cfg;
      dflt_fmt = new();
      vmm_rtl_config::default_file_fmt = dflt_fmt;
      RTLCFG_END
      TST_EXPL_START
      MACRO_START
      registry = new;
      registry.run(env);
      MACRO_END
      NORMAL_START
      env.run();
      NORMAL_END
      TST_EXPL_END
      TST_IMPL_START 
      vmm_simulation::list();
      vmm_simulation::run_tests();
      TST_IMPL_END
   end

endprogram: PB

`endif // PB__SV

