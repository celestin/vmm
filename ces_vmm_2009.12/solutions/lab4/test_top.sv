`timescale 1ns/100ps
module test_dut_top;
  parameter simulation_cycle = 100 ;
  reg  SystemClock ;
  router_io sigs(SystemClock);
  router dut(
    .reset_n ( sigs.reset_n ),
    .clock ( sigs.clk ),
    .frame_n ( sigs.frame_n ),
    .valid_n ( sigs.valid_n ),
    .din ( sigs.din ),
    .dout ( sigs.dout ),
    .busy_n ( sigs.busy_n ),
    .valido_n ( sigs.valido_n ),
    .frameo_n ( sigs.frameo_n )
  );

  initial begin
    $timeformat(-9, 1, "ns", 10);
    SystemClock = 0 ;
    forever begin
      #(simulation_cycle/2) 
        SystemClock = ~SystemClock ;
    end
  end
  
endmodule  
