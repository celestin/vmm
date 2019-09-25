//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`timescale 1ns/1ns

`include "vmm_wa_flags.sv"

`include "tcp_env.sv"

program p;

tcp_env env = new;

// Example 5-42
class my_action extends tcp_client_action;
   constraint never_rst {
      if (action == OPEN) pkt.rst == 0;
   }
endclass: my_action

initial
begin
   env.build();
   begin
      my_action act = new;
      env.sessions.randomized_action = act;
   end
   env.sessions.log.set_verbosity(vmm_log::DEBUG_SEV);
   env.server.log.set_verbosity(vmm_log::DEBUG_SEV);
   env.run();
end

endprogram
