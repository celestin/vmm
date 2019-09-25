/***************************************************************************
  *******************************************************************************
 *
 * Functional coverage model object
 *
 *******************************************************************************
 */

`ifndef _COVERAGE_SV_
`define _COVERAGE_SV_

class coverage_model ;

   fpu_trans tr;
   event cover_it;

   covergroup fpu @(cover_it);
      tr_op: coverpoint tr.op {
         option.weight = 0;
      }
      tr_rmode: coverpoint tr.rmode {
         option.weight = 0;
      }
      tr_opa_sign: coverpoint tr.opa.sign {
         option.weight = 0;
      }
      tr_opa_significand: coverpoint tr.opa.significand {
         option.weight = 0;
      }
      tr_opa_exponent: coverpoint tr.opa.exponent {
         option.weight = 0;
      }
      tr_opb_sign: coverpoint tr.opb.sign {
         option.weight = 0;
      }
      tr_opb_significand: coverpoint tr.opb.significand {
         option.weight = 0;
      }
      tr_opb_exponent: coverpoint tr.opb.exponent {
         option.weight = 0;
      }

      x_op_rmode: cross tr_op, 
                        tr_rmode, 
                        tr_opa_sign, 
                        tr_opa_significand,  
                        tr_opa_exponent, 
                        tr_opb_sign, 
                        tr_opb_significand, 
                        tr_opb_exponent;
      
   endgroup

   task cover_this(fpu_trans tr) ;
      this.tr = tr;
      ->this.cover_it;
   endtask: cover_this
endclass: coverage_model


`endif
