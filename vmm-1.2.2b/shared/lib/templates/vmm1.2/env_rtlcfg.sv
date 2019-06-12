//
// Template for VMM-compliant verification environment
// <VNAME>     Name of the Env 
// <XACT>      Name of the master driver
// <REC>       Name of the slave receiver 
// [filename]  VNAME_rtl_config
//

`ifndef VNAME_RTL_CONFIG__SV
`define VNAME_RTL_CONFIG__SV

class env_config extends vmm_rtl_config;

   `vmm_typename(env_config)
   SING_DRV_START
   rand XACT_config mst_cfg;
   SING_DRV_END
   MULT_DRV_START
   rand XACT_config mst_cfg_RPTNO;  //VMMGEN_RPT_ON_XACT
   MULT_DRV_END
   GEN_SL_RCVR_START
   rand REC_config slv_cfg;
   GEN_SL_RCVR_END
   //ToDo: Add declaration if any other RTL config objects are added  
  
   function new(string name = "", vmm_rtl_config parent = null);
      super.new(name, parent);
   endfunction: new

   function void build_config_ph();
      SING_DRV_START
      mst_cfg = new("mst_cfg", this);
      SING_DRV_END
      MULT_DRV_START
      mst_cfg_RPTNO = new("mst_cfg_RPTNO", this);  //VMMGEN_RPT_ON_XACT
      MULT_DRV_END
      GEN_SL_RCVR_START
      slv_cfg = new("slv_cfg", this);
      GEN_SL_RCVR_END
      //ToDo: instatiate all the declared RTL config handles
   endfunction: build_config_ph

endclass: env_config

`endif // VNAME_RTL_CONFIG__SV
