//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`ifndef UTOPIA_IF__SV
`define UTOPIA_IF__SV

interface utopia1_if;

   wire [7:0] TxData;
   wire       TxSOC;
   wire       TxEnb;
   wire       TxClav;
   wire       TxClk;
   wire [7:0] RxData;
   wire       RxSOC;
   wire       RxEnb;
   wire       RxClav;
   wire       RxClk;

   parameter setup_time = 1;
   parameter hold_time  = 0;

   clocking atx @ (posedge TxClk);
      //default input setup_time output hold_time;
      output TxData, TxSOC, TxEnb;
      input  TxClav;
   endclocking

   clocking arx @ (posedge RxClk);
      //default input setup_time output hold_time;
      input RxData, RxSOC, RxClav;
      output RxEnb;
   endclocking

   modport atm_layer (clocking atx,
                      clocking arx);


   clocking ptx @ (posedge TxClk);
      //default input setup_time output hold_time;
      input  TxData, TxSOC, TxEnb;
      output TxClav;
   endclocking

   clocking prx @ (posedge RxClk);
      //default input setup_time output hold_time;
      output RxData, RxSOC, RxClav;
      input  RxEnb;
   endclocking

   modport phy_layer (clocking ptx,
                      clocking prx);


   clocking tx @ (posedge TxClk);
      //default input setup_time output hold_time;
      input  TxData, TxSOC, TxEnb, TxClav;
   endclocking

   clocking rx @ (posedge RxClk);
      //default input setup_time output hold_time;
      input RxData, RxSOC, RxEnb, RxClav;
   endclocking

   modport passive (clocking tx,
                    clocking rx);

endinterface: utopia1_if

`endif
