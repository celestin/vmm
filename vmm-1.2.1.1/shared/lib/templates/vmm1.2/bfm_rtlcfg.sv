//
// Template for VMM-compliant verification environment
// <XACT>      Name of the master driver
// [filename]  XACT_rtl_config
//

`ifndef XACT_RTL_CONFIG__SV
`define XACT_RTL_CONFIG__SV

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

`endif // XACT_RTL_CONFIG__SV
