//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "vmm_wa_flags.sv"

`include "utopia_mgmt.sv"

// Example 4-96
`utopia_mgmt(tb_top.host0)
`utopia_mgmt(tb_top.host1)
   
class tb_env extends vmm_env;
   utopia_mgmt host[2];

   virtual function void build();
      \tb_top.host0.utopia_mgmt host0 = new(0);
      \tb_top.host1.utopia_mgmt host1 = new(1);

      host[0] = host0;
      host[1] = host1;
   endfunction: build
endclass: tb_env
