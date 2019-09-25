//
// Template for VMM-compliant transaction descriptor
//

`ifndef PACKET__SV
`define PACKET__SV

class Packet extends vmm_data;

   // ToDo: Add relevant class properties to define all transactions
   rand bit[3:0] sa, da;
   rand bit[7:0] payload[$];
        int      valid_sa[$];
        int      valid_da[$];

   // ToDo: Modify/add symbolic transaction identifiers to match
   typedef enum {IS_OK, ERROR} status_e;
   rand status_e status;

   constraint Packet_valid {
      // ToDo: Define constraint to make descriptor valid
      status == IS_OK;
      payload.size inside {[1:32]};
      if (valid_sa.size == 0) sa inside {[0:15]};
      else sa inside valid_sa;
      if (valid_da.size == 0) da inside {[0:15]};
      else da inside valid_da;
   }

   `vmm_data_member_begin(Packet)
      // ToDo: add properties using macros here
      `vmm_data_member_enum(status, DO_ALL-DO_COMPARE)
      `vmm_data_member_scalar(sa, DO_ALL-DO_COMPARE)
      `vmm_data_member_scalar(da, DO_ALL)
      `vmm_data_member_scalar_array(payload, DO_ALL)
      `vmm_data_member_scalar_array(valid_sa, DO_COPY+DO_PRINT)
      `vmm_data_member_scalar_array(valid_da, DO_COPY+DO_PRINT)
   `vmm_data_member_end(Packet)

   function void pre_randomize();
      foreach (valid_sa[i])
         if (!(valid_sa[i] inside {[0:15]}))
            `vmm_fatal(log, $psprintf("Invalid sa %0d", valid_sa[i]));
      foreach (valid_da[i])
         if (!(valid_da[i] inside {[0:15]}))
            `vmm_fatal(log, $psprintf("Invalid da %0d", valid_da[i]));
   endfunction: pre_randomize

   function void post_randomize();
      `vmm_debug(log, this.psdisplay());
   endfunction: post_randomize

endclass: Packet


`vmm_channel(Packet)
`vmm_atomic_gen(Packet, "Packet")
`vmm_scenario_gen(Packet, "Packet")

`endif // PACKET__SV
