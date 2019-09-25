//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

//
// Test producer -> Consumer
//

program test;

`include "producer.sv"
`include "consumer.sv"

initial
begin
   producer src = new;
   consumer snk = new(src.out_chan);

   snk.start_xactor();
   src.start_xactor();

   src.notify.wait_for(src.DONE);
end

endprogram: test
