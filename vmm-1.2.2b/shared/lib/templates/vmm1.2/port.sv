//
// Template for VMM-compliant transaction descriptor
// <IF>      Name of Interface 
// <PRT>     Name of interface port/wrapper class
// [filename] PRT

`ifndef PRT__SV
`define PRT__SV

class PRT extends vmm_data;

   `vmm_typename(PRT)
   static vmm_log log = new("PRT", "object");
   virtual IF.master iport_mst;
   GEN_SL_RCVR_START
   virtual IF.slave iport_slv;
   GEN_SL_RCVR_END
   virtual IF.passive iport_mon;

   function new(string name,
                virtual IF iport
                );
      super.new(this.log);
      this.iport_mst = iport;
      this.iport_mon = iport;
      GEN_SL_RCVR_START
      this.iport_slv = iport;
      GEN_SL_RCVR_END
   endfunction: new

endclass: PRT

`endif // PRT__SV
