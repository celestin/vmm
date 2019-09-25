//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

import vmm::*;
import atm::*;

`include "utopia1_if.sv"

package utopia1;

program

class utopia1_cfg;
   typedef enum {OCTET, CELL} handshaking_t;
   rand handshaking_t handshaking

   rand bit use_udf_channel;
endclass: utopia1_cfg


class utopia1_udf extends vmm_data;
   rand bit [7:0] data;

   extern function new();
   
   extern virtual function string psdisplay(string prefix = "");

   extern virtual function bit is_valid(bit     silent = 1,
                                        integer kind   = -1);

   extern virtual           function vmm_data allocate();
   extern virtual           function vmm_data copy(vmm_data cpy = null);
   
   extern virtual function bit compare(       vmm_data to,
                                       output string   diff,
                                              integer  kind = -1);

   extern virtual function int unsigned byte_size(integer kind = -1);
   extern virtual function int unsigned byte_pack(output byte         bytes[],
                                                  int unsigned offset = 0,
                                                  integer      kind   = -1);
   extern virtual function int unsigned byte_unpack(bit [7:0]    bytes[],
                                                    int unsigned offset = 0,
                                                    integer      kind   = -1);

   extern virtual function bit  load(integer file);
   extern virtual function void save(integer file);
endclass: utopia1_udf
`vmm_channel(utopia1_udf)


`include "utopia1_atm.sv"
`include "utopia1_phy.sv"
`include "utopia1_mon.sv"

endprogram
