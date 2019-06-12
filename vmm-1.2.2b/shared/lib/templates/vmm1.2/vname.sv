//
// Template for VMM-compliant verification environment
// <CFG>       Name of the configuration class
// <SB>        Name of vmm_sb_ds Scoreboard class
// <TR>        Name of the transaction descriptor
// <XACT>      Name of the driver
// <MON>       Name of the monitor class
// <COV>       Name of the coverage class
//

`ifndef VNAME__SV
`define VNAME__SV

`include "vmm.sv"
`include "vmm_sb.sv"
RAL_START
`include "vmm_ral.sv"
RAL_END
PERF_START
`include "vmm_perf.sv"
PERF_END

`include "PRT.sv"
RTLCFG_START
SING_DRV_START  
`include "XACT_rtlcfg.sv"
SING_DRV_END
MULT_DRV_START
`include "XACT_rtlcfg.sv"  //VMMGEN_RPT_ON_XACT
MULT_DRV_END
GEN_SL_RCVR_START
`include "VNAME_rec_rtlcfg.sv" 
GEN_SL_RCVR_END
`include "VNAME_env_rtlcfg.sv" 
RTLCFG_END
`include "CFG.sv"
`include "TR.sv"   //VMMGEN_RPT_ON_TR
SCN_GEN_START
`include "SCEN.sv"
//ToDo: Include required scenario files files
SCN_GEN_END
SCBD_EN_START
`include "SB.sv"
SCBD_EN_END
MS_GEN_START
//ToDo: Include required scenario files files
`include "VNAME_ms_scen.sv"
MS_GEN_END
SING_DRV_START
`include "XACT.sv"
SING_DRV_END
MULT_DRV_START
`include "XACT.sv"  //VMMGEN_RPT_ON_XACT
//ToDo: If you have multiple drivers in the environment, Include other drivers here. 
MULT_DRV_END
SCBD_EN_START
`include "XACT_sb_cb.sv"
SCBD_EN_END
`include "MON.sv"
MNTR_OBS_MTHD_ONE_START
SCBD_EN_START
`include "MON_sb_cb.sv"
SCBD_EN_END
`include "MON.sv"
MNTR_OBS_MTHD_ONE_END
GEN_SL_RCVR_START
`include "REC.sv"
GEN_SL_RCVR_END
`include "COV.sv"
MNTR_OBS_MTHD_ONE_START
`include "MON_2cov_connect.sv"
MNTR_OBS_MTHD_ONE_END
MNTR_OBS_MTHD_TWO_START
MNTR_OBS_MTHD_TWO_Q_START
`include "MON_2cov_connect.sv"
MNTR_OBS_MTHD_TWO_Q_END
MNTR_OBS_MTHD_TWO_END
RAL_START
SING_DM_START
`include "XACT_ral.sv"
SING_DM_END
MULT_DM_START
`include "XACT_DN1_ral.sv"
`include "XACT_DN2_ral.sv"
//ToDo : Include other RAL BFM files, if more than two domains are used.

MULT_DM_END
`include "ral_VNAME.sv"
RAL_END
// ToDo: Add additional required `include directives

`endif // VNAME__SV
