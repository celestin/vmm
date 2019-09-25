//
// Test configuration descriptor
//

`ifndef _TEST_CFG_SV_
`define _TEST_CFG_SV_

typedef class fpu_cfg;

class test_cfg ;
   rand int run_for;
   rand fpu_cfg fpu;

   constraint test_cfg1 {
      run_for > 0;
   }

   constraint reasonable {
      run_for < 50;
   }

   function new() ;
      this.fpu = new;
   endfunction: new
endclass: test_cfg

`endif
