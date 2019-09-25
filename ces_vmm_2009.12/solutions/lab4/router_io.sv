`ifndef ROUTER_IO__SV
`define ROUTER_IO__SV

interface router_io(input bit clk);

   parameter setup = 1/*ns*/;
   parameter clk2q = 1/*ns*/;

   logic  reset_n ;
   logic [15:0] frame_n ;
   logic [15:0] valid_n ;
   logic [15:0] din ;
   logic [15:0] dout ;
   logic [15:0] busy_n ;
   logic [15:0] valido_n ;
   logic [15:0] frameo_n ;

   clocking mclk @(posedge clk);
      output  reset_n;
      output  frame_n;
      output  valid_n;
      output  din;
      input   busy_n;
   endclocking: mclk

   clocking sclk @(posedge clk);
      input  dout;
      input  valido_n;
      input  frameo_n;
   endclocking: sclk

   modport master(clocking mclk, output reset_n);
   modport slave(clocking sclk);

endinterface: router_io

`endif
