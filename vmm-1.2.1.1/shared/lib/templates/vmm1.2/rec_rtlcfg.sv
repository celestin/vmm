//
// Template for VMM-compliant verification environment
// <REC>       Name of the slave receiver 
// [filename]  REC_rtl_config
//

`ifndef REC_RTL_CONFIG__SV
`define REC_RTL_CONFIG__SV

class REC_config extends vmm_rtl_config;

   `vmm_typename(REC_config)
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

`endif // REC_RTL_CONFIG__SV
