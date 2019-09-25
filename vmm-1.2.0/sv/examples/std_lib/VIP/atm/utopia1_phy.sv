//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

virtual class utopia1_phy_callbacks extends vmm_xactor_callbacks;
   virtual task pre_cell_tx(utopia1_phy_layer xactor,
                            ref atm_cell      cell
                            ref utopia1_udf   udf,
                            ref bit           drop)
   endtask

   virtual task post_cell_tx(utopia1_phy_layer xactor,
                             const atm_cell    cell
                             const utopia1_udf udf)
   endtask

   virtual task pre_symbol_tx(utopia1_phy_layer xactor,
                              ref bit [7:0]     symbol,
                              ref bit           SOC,
                              ref bit           Enb,
                              const bit         Clav,
                              ref bit           drop)
   endtask


   virtual task post_cell_rx(utopia1_phy_layer xactor,
                             const atm_cell    cell
                             const utopia1_udf udf)
   endtask

   virtual task post_symbol_rx(utopia1_phy_layer xactor,
                               const bit [7:0]   symbol,
                               const bit         SOC,
                               ref bit           Enb,
                               const bit         Clav)
   endtask

endclass: utopia1_phy_callbacks


class utopia1_phy_layer extends vmm_xactor;

   virtual utopia1_if.phy_layer if;

   atm_cell_channel cell_out_chan;
   atm_cell_channel cell_in_chan;

   utopia1_udf_channel udf_out_chan;
   utopia1_udf_channel udf_in_chan;

   local utopia1_cfg cfg;
   local atm_cell    rx_factory;

   extern function new(string                       inst,
                       int unsigned                 stream_id = -1,
                       utopia1_cfg                  cfg,
                       atm_cell                     rx_factory,
                       virtual utopia1_if.phy_layer if,
                       atm_cell_channel             cell_out_chan = null,
                       atm_cell_channel             cell_in_chan  = null,
                       utopia1_udf_channel          udf_out_chan  = null,
                       utopia1_udf_channel          udf_in_chan   = null);

   extern virtual function void reconfigure(utopia1_cfg cfg        = null,
                                            atm_cell    rx_factory = null);
   extern virtual function void reset_xactor(rst_typ typ = SOFT_RST);

   extern protected virtual task main();
   
endclass: utopia1_phy_layer
