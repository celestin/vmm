/***************************************************************************
*******************************************************************************
*
* Class retaining all configuration parameters
* that do pertain to the FPU from open cores
*
*******************************************************************************
*/

`ifndef _FPU_CFG_SV
`define _FPU_CFG_SV

class fpu_cfg ;
  
  // Maximum number of transactions
  rand int max_trans_cnt;

  // basic constraint applied to max_trans_cnt
  constraint basic {
    (max_trans_cnt > 0) && (max_trans_cnt < 10);
  }
endclass: fpu_cfg

`endif
