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

`timescale 1ns/100ps
module router_test_top;
  parameter simulation_cycle = 100 ;
  reg  SystemClock ;
  router_io top_io(SystemClock);
  test tb(top_io);
  router dut(
    .reset_n ( top_io.reset_n ),
    .clock ( top_io.clock ),
    .frame_n ( top_io.frame_n ),
    .valid_n ( top_io.valid_n ),
    .din ( top_io.din ),
    .dout ( top_io.dout ),
    .busy_n ( top_io.busy_n ),
    .valido_n ( top_io.valido_n ),
    .frameo_n ( top_io.frameo_n )
  );

  initial begin
    $timeformat(-9, 1, "ns", 10);
    $vcdpluson;
    SystemClock = 0 ;
    forever begin
      #(simulation_cycle/2) 
        SystemClock = ~SystemClock ;
    end
  end
  
endmodule  
