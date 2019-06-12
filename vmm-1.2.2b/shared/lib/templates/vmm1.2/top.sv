//
// Template for Top module
// <MOD>        Name of top module
// <IF>         Name of physical interface
// <PB>         Name of the program block
//

`ifndef MOD__SV
`define MOD__SV

module MOD();

   logic ck1;
   logic ck2;
   logic rst_n;

   // Clock Generation
   parameter sim_cycle = 10;
   
   // Reset Delay Parameter
   parameter rst_delay = 50;

   always 
      begin
         ck1 = #(sim_cycle/2) ~ck1;
         ck2 = #(sim_cycle/2) ~ck2;
      end

   SING_DRV_START
   IF intf(ck1,ck2);
   SING_DRV_END
   MULT_DRV_START
   IF intf[ INTF_COUNT] (ck1,ck2);
   MULT_DRV_END
   PB test(intf); 
   
   // ToDo: Include Dut instance here
  
   //Driver reset depending on rst_delay
   initial
      begin
         ck1   = 0;
         ck2   = 0;
         rst_n = 1;
      #1 rst_n = 0;
         repeat (rst_delay) @(ck1);
         rst_n = 1'b1;
         @(ck1);
   end

endmodule: MOD

`endif // MOD__SV
