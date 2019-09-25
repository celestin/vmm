//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

// Example 4-96
`include "tb_top.sv"

`include "vmm.sv"

program test;

`include "tb_env.sv"
tb_env env = new;

initial
begin
   env.build();
   `vmm_note(env.host[0].log, "Message from Host #0");
   `vmm_note(env.host[1].log, "Message from Host #1");
end

endprogram: test
