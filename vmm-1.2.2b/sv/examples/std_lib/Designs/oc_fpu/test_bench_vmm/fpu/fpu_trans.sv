//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

/***************************************************************************
 *******************************************************************************
 *
 * Basic Transaction Structure
 *
 *******************************************************************************
 */

`ifndef _FPU_TRANS_SV_ 
`define _FPU_TRANS_SV_ 

class operand;
    rand bit sign;
    rand bit[22:0] significand;
    rand bit[7:0] exponent;

    //ToDo: need to fix if there is a log
    virtual function string psdisplay(string prefix = "");
       return $psprintf("%s%b %x %x",
                prefix, this.sign, this.exponent, this.significand);
    endfunction: psdisplay

endclass: operand

//ToDo: should be class local enums  when they are supported.
typedef enum {ADD, SUB, MUL, DIV, I2F, F2I, REM, RESERVE} op_e;
    //I2F - int to float and F2I - Float to Integer
    //REM - reminder(spec says future function)

typedef enum {r2even, r2zero, r2plusinf, r2minusinf} rmode_e;
    //r2even - round to nearest even
    //r2zero - round to zero
    //r2plusinf - round to +INF
    //r2minusinf - round to -INF

class fpu_trans extends vmm_data ;


    // Data Logger
    static vmm_log log = new("fpu_trans", "class");

    // Random fields
    rand op_e   op;
    rand rmode_e  rmode;

    //prefer contained classes in this case
    //  hence make sure these are newed
    //  before randomization (constructor can take care of it)
    //  They always should exist, hence
    //  its not an issue in this case.
    rand operand opa;
    rand operand opb;

    constraint op_cst {
        //ToDo: implement full set
        //   op inside { ADD, SUB, MUL, DIV };
        op inside { ADD, SUB };
    }

    // Constructor
    function new();
       super.new(this.log);
       this.opa = new;
       this.opb = new;
    endfunction: new

    // Methods derived from vmm_data
    virtual function string psdisplay(string prefix = "");
       return $psprintf("%sop=%s rmode=%s\n%s\n%s", prefix, this.op, this.rmode,
                        this.opa.psdisplay({prefix, "OpA: "}),
                        this.opb.psdisplay({prefix, "OpB: "}));
    endfunction: psdisplay

    virtual function vmm_data allocate();
       fpu_trans tr = new;
       allocate = tr;
    endfunction: allocate

    virtual function vmm_data copy(vmm_data cpy = null);
       fpu_trans to = null;

       if (cpy == null) begin
	   to = new;
       end else if ($cast(to, cpy)) begin
	   `vmm_fatal(this.log,
                      "Attempting to copy to a non-fpu_trans instance");
	   copy = null;
	   return;
       end

       super.copy_data(to);

       to.op = this.op;
       to.rmode = this.rmode;
       to.opa.sign = this.opa.sign;
       to.opa.significand = this.opa.significand;
       to.opa.exponent = this.opa.exponent;
       to.opb.sign = this.opb.sign;
       to.opb.significand = this.opb.significand;
       to.opb.exponent = this.opb.exponent;

       copy = to;
    endfunction: copy

    virtual function bit compare(vmm_data to,
            output string diff,
            input int kind = -1);
       fpu_trans tr;
       compare = 1;
       
       if (!$cast(tr, to)) begin
	 diff = "Not a fpu_trans instance";
	 compare = 0;
	 return;
       end
       
       if(this.op != tr.op) begin
	   $sformat(diff,"op mismatch %d != %d\n",this.op,tr.op) ;
	   compare = 0;
       end
       
       if(this.rmode != tr.rmode) begin
	   $sformat(diff,"%s rmode mismatch %d != %d\n", diff,this.rmode,tr.rmode);
	   compare = 0;
       end
       
       if(this.opa.sign != tr.opa.sign) begin
	   $sformat(diff,"%s opa sign mismatch %b != %b\n", diff, this.opa.sign, tr.opa.sign);
	   compare = 0;
       end
       
       if(this.opa.significand != tr.opa.significand) begin
	   $sformat(diff,"%s opa significand mismatch %x != %x\n", diff, this.opa.significand, tr.opa.significand);
	   compare = 0;
       end

       if(this.opa.exponent != tr.opa.exponent) begin
	   $sformat(diff,"%s opa exponent mismatch %x != %x\n", diff, this.opa.exponent, tr.opa.exponent);
	   compare = 0;
       end
       
       if(this.opb.sign != tr.opb.sign) begin
	   $sformat(diff,"%s opb sign mismatch %b != %b\n", diff, this.opb.sign, tr.opb.sign);
	   compare = 0;
       end
       
       if(this.opb.significand != tr.opb.significand) begin
	   $sformat(diff,"%s opb significand mismatch %x != %x\n", diff, this.opb.significand, tr.opb.significand);
	   compare = 0;
       end

       if(this.opb.exponent != tr.opb.exponent) begin
	   $sformat(diff,"%s opb exponent mismatch %x != %x\n", diff, this.opb.exponent, tr.opb.exponent);
	   compare = 0;
       end

    endfunction: compare

    virtual function int unsigned byte_size(int kind = -1);
       byte_size = 0;
    endfunction: byte_size
 
    virtual function int unsigned byte_pack(ref logic [7:0] bytes[],
            input int unsigned offset = 0,
            input int kind   = -1);
       byte_pack = 0;
    endfunction: byte_pack

    virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
            input int unsigned offset = 0,
            int len   = -1,
            int kind   = -1);
       byte_unpack = 0;
    endfunction: byte_unpack

endclass: fpu_trans

// Declare a specific vmm_channel of fpu_trans
`vmm_channel(fpu_trans)


`endif
