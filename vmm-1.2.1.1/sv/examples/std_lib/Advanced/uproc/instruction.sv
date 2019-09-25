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

`include "opcode.sv"

class instruction extends vmm_data;
  static vmm_log log = new ("instruction", "class");
  rand opcode 	op[2];

  // memory load and store can only appear in slot 0
  // eg.
  // do not allow cases like		ADD R0, R1, R2 	;  SB R4, 0x0120 (R5)
  constraint slot0_only_good {				
    !(op[1].kind inside { opcode::LW, opcode::SB });
  }

  // operations on the same instruction must not write to the same
  // register
  // eg.
  // do not allow cases like		ADD R0, R1, R2	; SLL R0, R3, R1
  constraint writing_two_different_regs_valid { 	
    op[0].rd != op[1].rd;
  }

  // only op[0] can be a label,
  constraint deal_with_labels_valid {
    (op[0].kind == opcode::LABEL) -> (op[1].kind == opcode::LABEL);
    op[1].label_suffix == op[0].label_suffix;
    (op[0].kind != opcode::LABEL) -> (op[1].kind != opcode::LABEL);
  }
  
  function new();
    super.new (log);
    foreach (op[i]) op[i] = new;
  endfunction // new
   

   virtual function vmm_data copy(vmm_data cpy = null);
      
    instruction to;
    
    // New an instance is none is passed in
    if (cpy == null) begin
      to = new;
    end
    else begin
      // Copying to an existing instance. 
      if (!$cast(to, cpy)) begin
         `vmm_fatal(this.log, "Attempting to copy to a non instruction instance");
        return cpy;
      end
    end
      
    super.copy_data(to);
    $cast(to.op[0], this.op[0].copy());
    $cast(to.op[1], this.op[1].copy());

    to.op[0].stream_id = this.stream_id;
    to.op[0].scenario_id = this.scenario_id;
    to.op[0].data_id = this.data_id;
    
    to.op[1].stream_id = this.stream_id;
    to.op[1].scenario_id = this.scenario_id;
    to.op[1].data_id = this.data_id;    
    
    // Assign to output
    copy = to;       
   endfunction // vmm_data
   

   virtual function vmm_data allocate();
    instruction tr = new;
    allocate = tr;
   endfunction // vmm_data
   
  
  // Example:		SB R4, 0x0120 (R5)  ; ADD R0, R1, R2
   virtual function string psdisplay (string prefix = "");
      
    if (op[0].kind != opcode::LABEL) begin
       $sformat (psdisplay, "%10s %-50s;%-50s\n", prefix, op[0].psdisplay(), op[1].psdisplay());
    end
    else begin
       $sformat (psdisplay, "%10s %-50s;\n", prefix, op[0].psdisplay());
    end
   endfunction // string

endclass // instruction

`vmm_channel (instruction)
   
`vmm_scenario_gen (instruction, "Instruction")   
