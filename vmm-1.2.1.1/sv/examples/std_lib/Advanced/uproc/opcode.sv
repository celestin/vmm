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

`include "vmm.sv"

class opcode extends vmm_data;
   static vmm_log log = new ("opcode", "class");
   
   typedef enum {
      NOP, LW, SB, ADD, ADDI, SRL, SLL, XOR, BNE, LABEL 
   } kind_e;
   
   typedef enum {
      NO_OPERATION, LOAD_STORE, COMPUTE, CONTROL, LABEL_NAME
   } opcode_type_e;
   
   rand kind_e          kind;
   rand opcode_type_e   opcode_type;
   
   rand bit [5:0]       rs;
   rand bit [5:0]       rt;
   rand bit [5:0]       rd;
   rand bit [9:0]       imm;

   rand bit [9:0]       from;
   rand bit [9:0]       to;
   rand bit [9:0]       label_suffix;
   
   constraint only_48_registers_valid {
     rd inside {[0:47]};
     rs inside {[0:47]};
     rt inside {[0:47]};
   }
      
   constraint opcode_type_valid {
     (opcode_type == NO_OPERATION) -> kind inside { NOP };
     (opcode_type == LOAD_STORE)   -> kind inside { LW, SB };
     (opcode_type == COMPUTE)      -> kind inside { ADD, ADDI, SRL, SLL, XOR }; 
     (opcode_type == CONTROL)      -> kind inside { BNE };
     (opcode_type == LABEL_NAME)   -> kind inside { LABEL };
   }

   virtual function vmm_data copy(vmm_data cpy = null);
      opcode to;
      // New an instance is none is passed in
      if (cpy == null) begin
	 to = new;
      end
      else begin
	 // Copying to an existing instance. 
	 if ($cast(to, cpy)) begin
	    `vmm_fatal(this.log, "Attempting to copy to a non opcode instance");
	    return cpy;
	 end
      end // else: !if(cpy == null)
      super.copy_data(to);

      // Copy local data fields
      to.kind = this.kind;
      to.opcode_type = this.opcode_type;

      to.rd = this.rd;
      to.rt = this.rt;
      to.rs = this.rs;

      to.imm = this.imm;
      to.from = this.from;
      to.to = this.to;
      to.label_suffix = this.label_suffix;

      // assign to output
      copy = to;
   endfunction // vmm_data
   
   virtual function vmm_data allocate();
      opcode tr = new;
      allocate = tr;
   endfunction // vmm_data
   
   
   // Example:    LW   R0, 0x50 (R1)
   //      BNE  R1, R2, LABEL_000005
   virtual function string psdisplay (string prefix = "");
      string str;
      case (this.kind) 
	NOP    : $sformat (str, "%0s\tNOP                                ", prefix);
	LW     : $sformat (str, "%0s\tLW    R%0d, 0x%3x(R%0d)               ", prefix, rd, imm, rs);
	SB     : $sformat (str, "%0s\tSB    0x%3x(R%0d)                     ", prefix, imm, rs);
	ADD    : $sformat (str, "%0s\tADD   R%0d, R%0d, R%0d                ", prefix, rd, rs, rt);
	ADDI   : $sformat (str, "%0s\tADDI  R%0d, R%0d, 0x%3x               ", prefix, rd, rs, imm);
	SRL    : $sformat (str, "%0s\tSRL   R%0d, R%0d, 0x%3x               ", prefix, rd, rs, imm);           
	SLL    : $sformat (str, "%0s\tSLL   R%0d, R%0d, 0x%3x               ", prefix, rd, rs, imm);
	XOR    : $sformat (str, "%0s\tXOR   R%0d, R%0d, R%0d                ", prefix, rd, rs, rt);
	BNE    : $sformat (str, "%0s\tBNE   R%0d, R%0d, LABEL_scn%0d_%x     ", prefix, rs, rt, scenario_id, to);
	LABEL  : $sformat (str, "%0sLABEL_scn%0d_%x", prefix, scenario_id, label_suffix);
      endcase // case (this.kind)
      
`ifdef DEBUG  
      if (this.kind == BNE) begin
	 $sformat (str, "%0s (from=%0d,to=%0d,label_suffix=%0d)", str, from, to, label_suffix);
      end
`endif
      
      psdisplay = str;
      
   endfunction // string

   function new ();
      super.new(log);
   endfunction // new
   

endclass // opcode
