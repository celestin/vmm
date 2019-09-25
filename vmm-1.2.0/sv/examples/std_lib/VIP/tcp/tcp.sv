//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`ifndef TCP__SV
`define TCP__SV

`include "vmm.sv"


`ifdef VIP_IN__PACKAGE
package tcp;
`endif

`ifdef VIP_IN_ANONYMOUS_PROGRAM
program;

timeunit 1ns;
`endif

`include "packet.sv"
`include "sessions.sv"
`include "server.sv"

`ifdef VIP_IN_ANONYMOUS_PROGRAM
endprogram
`endif

`ifdef VIP_IN_PACKAGE
endpackage: tcp
`endif

`endif
