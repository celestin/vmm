//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

class utopia1_mon extends vmm_xactor;

   virtual utopia1_if.passive if;

   atm_cell_channel cell_to_atm_chan;
   atm_cell_channel cell_to_phy_chan;

   utopia1_udf_channel udf_to_atm_chan;
   utopia1_udf_channel udf_to_phy_chan;

   local utopia1_cfg cfg;
   local atm_cell    to_atm_factory;
   local atm_cell    to_phy_factory;

   extern function new(string                     inst,
                       int unsigned               stream_id = -1,
                       utopia1_cfg                cfg,
                       atm_cell                   to_atm_factory,
                       atm_cell                   to_phy_factory,
                       virtual utopia1_if.passive if,
                       atm_cell_channel           cell_to_atm_chan = null,
                       atm_cell_channel           cell_to_phy_chan = null,
                       utopia1_udf_channel        udf_to_atm_chan  = null,
                       utopia1_udf_channel        udf_to_phy_chan  = null);

   extern virtual function void reconfigure(utopia1_cfg cfg            = null,
                                            atm_cell    to_atm_factory = null,
                                            atm_cell    to_phy_factory = null);
);
   extern virtual function void reset_xactor(rst_typ typ = SOFT_RST);

   extern protected virtual task main();
   
endclass: utopia1_mon
