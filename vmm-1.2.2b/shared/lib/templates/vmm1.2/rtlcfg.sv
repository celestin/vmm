//
// Template for VMM-compliant verification environment
// <VNAME>     Name of the Env 
// <XACT>      Name of the master driver
// <REC>       Name of the slave receiver 
// [filename]  VNAME_rtl_config
//

`ifndef VNAME_RTL_CONFIG__SV
`define VNAME_RTL_CONFIG__SV

class XACT_config extends vmm_rtl_config;
 
   `vmm_typename(XACT_config)
   rand  bit mst_enable;
   string    kind = "XACT";
   //ToDo : Add the required RTL configuration parameters required for master 

   constraint cst_mst {
      mst_enable == 1;
   }
   `vmm_rtl_config_begin(XACT_config)
      `vmm_rtl_config_boolean(mst_enable, mst_enable)
      `vmm_rtl_config_string(kind, kind)
       //ToDo : Add the config macro for parameters declated
   `vmm_rtl_config_end(XACT_config)

   function new(string name = "", vmm_rtl_config parent = null);
      super.new(name, parent);
   endfunction: new

endclass: XACT_config
GEN_SL_RCVR_START


class REC_config extends vmm_rtl_config;

   rand  bit slv_enable;
   string    kind = "REC";
   //ToDo : Add the required RTL configuration parameters required for slave 

   constraint cst_slv {
     slv_enable == 1;
   }
   
`vmm_rtl_config_begin(REC_config)
   `vmm_rtl_config_boolean(slv_enable, slv_enable)  
   `vmm_rtl_config_string(kind, kind)
   //ToDo : Add the config macro for parameters declated
`vmm_rtl_config_end(REC_config)

   function new(string name = "", vmm_rtl_config parent = null);
      super.new(name, parent);
   endfunction: new

endclass: REC_config
GEN_SL_RCVR_END


class env_config extends vmm_rtl_config;

   rand XACT_config mst_cfg;
   GEN_SL_RCVR_START
   rand REC_config slv_cfg;
   GEN_SL_RCVR_END
   //ToDo: Add declaration if any other RTL config objects are added  
  
   function new(string name = "", vmm_rtl_config parent = null);
      super.new(name, parent);
   endfunction: new

   function void build_config_ph();
      mst_cfg = new("mst_cfg", this);
      GEN_SL_RCVR_START
      slv_cfg = new("slv_cfg", this);
      GEN_SL_RCVR_END
      //ToDo: instatiate all the declared RTL config handles
   endfunction: build_config_ph

endclass: env_config

`endif // VNAME_RTL_CONFIG__SV
