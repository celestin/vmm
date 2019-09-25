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


`define PHY_DL_SUBCHANS_PER_MAJOR_GROUP 6
`define PHY_DL_SUBCHANS_PER_MINOR_GROUP 4

`define PHY_10MHZ_UL_NUM_OF_SUBCHANNELS 35
`define PHY_10MHZ_DL_PUSC_NUM_OF_SUBCHANNELS 30
`define PHY_10MHZ_DL_FUSC_NUM_OF_SUBCHANNELS 16


class phy_tb_config extends vmm_object;
  rand int num_of_frames;
  int BW_MHz = 10;
  int frame_length  = 48;
  int IDcell = 0;

  rand int unsigned num_of_dl_pusc_subchannels;
  rand int unsigned num_of_dl_fusc_subchannels;
  rand int unsigned num_of_ul_subchannels;

  default constraint cst_phy_tb_config_default {
    num_of_frames == 2;

  }

  constraint cst_phy_tb_config_valid {
     if (BW_MHz == 10) {
	//num_of_dl_pusc_subchannels == `PHY_10MHZ_DL_PUSC_NUM_OF_SUBCHANNELS;
	num_of_dl_fusc_subchannels == `PHY_10MHZ_DL_FUSC_NUM_OF_SUBCHANNELS;
	//num_of_ul_subchannels == `PHY_10MHZ_UL_NUM_OF_SUBCHANNELS;
	num_of_ul_subchannels inside {[25 : 35]};
	num_of_dl_pusc_subchannels inside {[25 : 35]};
     }
  }

  constraint cst_user;

  vmm_log log;

  function new(string inst = "", vmm_object parent = null);
    super.new(parent, inst);
    log = new("phy_tb_config", "class");
  endfunction

  function void pre_randomize();
     bit is_set;
     num_of_dl_pusc_subchannels = vmm_opts::get_object_int(is_set, this, "num_of_dl_pusc_subchannels", 40, "SET num_of_dl_pusc_subchannels value");
     if (is_set) num_of_dl_pusc_subchannels.rand_mode(0);
     else `vmm_warning(log, "num_of_dl_pusc_subchannels was NOT set through vmm_opts");
  endfunction


   function string psdisplay(string prefix = "");
      psdisplay = { $psprintf("\t************** PHY_CFG ***************\n"),
                    $psprintf("\tnum_of_frames              : %0d\n", num_of_frames),
                    $psprintf("\tnum_of_dl_pusc_subchannels : %0d\n", num_of_dl_pusc_subchannels),
                    $psprintf("\tnum_of_dl_fusc_subchannels : %0d\n", num_of_dl_fusc_subchannels),
                    $psprintf("\tnum_of_ul_subchannels      : %0d\n", num_of_ul_subchannels)
                  };
   endfunction


endclass

