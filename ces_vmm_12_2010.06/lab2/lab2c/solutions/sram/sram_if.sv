interface sram_if #(RAM_ADDR_WDTH = 8) (input logic clk, ce_N, rdWr_N, input logic [RAM_ADDR_WDTH-1:0] ramAddr, inout wire [7:0] ramData);

   clocking cb @(posedge clk);
      input #1 ce_N;
      input #1 rdWr_N;
      input ramAddr;
      inout ramData;
   endclocking

   modport memprt(input ramAddr, inout ramData, input ce_N, input rdWr_N, clocking cb);
   modport monprt(input ramAddr, input ramData, input ce_N, input rdWr_N, clocking cb);
endinterface

