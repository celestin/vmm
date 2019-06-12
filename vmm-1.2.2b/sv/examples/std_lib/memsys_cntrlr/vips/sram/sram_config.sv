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

class sram_config extends vmm_rtl_config;
  typedef enum int {SIZE_256 = 256, SIZE_512 = 512, SIZE_1024 = 1024} sram_size_e;
  rand int          num_sram_devices;
  string            sram_size_str = "SIZE_256";
  rand sram_size_e  sram_size;

  constraint cst_sram_config_valid {
    num_sram_devices inside {1, 2, 4};
  }

  `vmm_rtl_config_begin(sram_config)
   `vmm_rtl_config_int(num_sram_devices, num_sram_devices)
   `vmm_rtl_config_string(sram_size_str, sram_size_str)
  `vmm_rtl_config_end(sram_config)

   function new(string name = "", vmm_rtl_config parent = null);
      super.new(name, parent);
   endfunction

   function void post_randomize();
     sram_size_str = $psprintf("%s", sram_size.name);
   endfunction

   function sram_size_e get_sram_size();
     case (sram_size_str)
        "SIZE_256"  : return SIZE_256;
        "SIZE_512"  : return SIZE_512;
        "SIZE_1024" : return SIZE_1024;
        default     : begin
                        `vmm_fatal(log, {"Unsupported SRAM size used for configuration", sram_size_str});
                      end
     endcase
   endfunction

   function int get_addr_width();
     case (sram_size_str)
        "SIZE_256"  : return 8;
        "SIZE_512"  : return 9;
        "SIZE_1024" : return 10;
        default     : return 8;
     endcase
   endfunction

endclass

