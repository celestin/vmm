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


class phy_color;
  rand bit [5:0] symbol_indx;
  rand bit [5:0] sub_chan_indx;
  bit [5:0] burst_indx;
  bit [5:0] zone_indx;
  bit colored = 0;
  
  function new(int i, int j, int brst_idx, int zone_idx);
    this.symbol_indx = i;
    this.sub_chan_indx = j;
    this.burst_indx = brst_idx;
    this.zone_indx = zone_idx;
  endfunction

  function string psdisplay(string prefix = "");
    psdisplay = $psprintf("%s Color:zone#%0d, burst#%0d, sub_chan_indx = %0d, symbol_indx = %0d\n", prefix, zone_indx, burst_indx, sub_chan_indx, symbol_indx);
  endfunction

  virtual function bit [15:0] get_color_val();
    bit [15:0] result = 0;
    result[5:0] = symbol_indx;
    result[13:8] = sub_chan_indx;
    get_color_val = result;
  endfunction

  virtual function bit [5:0] get_burst_index();
    get_burst_index = burst_indx;
  endfunction

  virtual function set_burst_index(bit [5:0] brst_indx);
    this.burst_indx = brst_indx;
    colored = 1;
  endfunction
 
  virtual function bit is_colored();
    is_colored = colored;
  endfunction

endclass





