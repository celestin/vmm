//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

virtual class atm_cell extends vmm_data;

   rand bit [15:0] vci;
   rand bit        clp;
   rand bit [ 2:0]  pt;
   rand bit [ 7:0]  hec;
   rand bit [ 7:0]  payload[48];

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
endclass: atm_cell


class atm_uni_cell extends atm_cell;

   rand bit [3:0] gfc;
   rand bit [7:0] vpi;

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

endclass: atm_uni_cell


class atm_nni_cell extends atm_cell;

   rand bit [11:0] vpi;

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

endclass: atm_nni_cell


`vmm_channel(atm_cell)

`vmm_channel(atm_uni_cell)
`vmm_atomic_gen(atm_uni_cell)

`vmm_channel(atm_nni_cell)
`vmm_atomic_gen(atm_nni_cell)



class atm_channel_to_uni_channel;
   atm_cell_channel     in_chan;
   atm_uni_cell_channel out_chan;

   extern function new(atm_cell_channel     in_chan  = null
                       atm_uni_cell_channel out_chan = null);

endclass: atm_channel_to_uni_channel


class uni_channel_to_atm_channel;
   atm_uni_cell_channel in_chan;
   atm_cell_channel     out_chan;

   extern function new(atm_uni_cell_channel in_chan  = null,
                       atm_cell_channel     out_chan = null);

endclass: uni_channel_to_atm_channel



class atm_channel_to_nni_channel;
   atm_cell_channel     in_chan;
   atm_nni_cell_channel out_chan;

   extern function new(atm_cell_channel     in_chan  = null
                       atm_nni_cell_channel out_chan = null);

endclass: atm_channel_to_nni_channel


class nni_channel_to_atm_channel;
   atm_nni_cell_channel in_chan;
   atm_cell_channel     out_chan;

   extern function new(atm_nni_cell_channel in_chan  = null,
                       atm_cell_channel     out_chan = null);

endclass: nni_channel_to_atm_channel
