//
// Template for VMM-compliant Coverage Class
// <COV>        Name of Coverage class
// <TR>         Name of Transaction descriptor class
//

`ifndef COV__SV
`define COV__SV

class COV;
   `vmm_typename(COV)
   event cov_event;
   TR tr;
   MNTR_OBS_MTHD_TWO_START
   MNTR_OBS_MTHD_TWO_NQ_START
   vmm_tlm_analysis_export #(COV,TR) cov_export;
   MNTR_OBS_MTHD_TWO_NQ_END
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START
   vmm_tlm_analysis_export #(COV,TR) cov_export;
   MNTR_OBS_MTHD_THREE_END
   
   covergroup cg_trans @(cov_event);
      coverpoint tr.kind;
      // ToDo: Add required coverpoints, coverbins
   endgroup: cg_trans


   function new();
      cg_trans = new;
      MNTR_OBS_MTHD_TWO_START
      MNTR_OBS_MTHD_TWO_NQ_START
      cov_export = new(this, "Coverage Analysis");
      MNTR_OBS_MTHD_TWO_NQ_END
      MNTR_OBS_MTHD_TWO_END
      MNTR_OBS_MTHD_THREE_START
      cov_export = new(this, "Coverage Analysis");
      MNTR_OBS_MTHD_THREE_END
   endfunction: new
   MNTR_OBS_MTHD_TWO_START 
   MNTR_OBS_MTHD_TWO_NQ_START


   virtual function write(int id= -1, TR tr);
      this.tr = tr;
      -> cov_event;
   endfunction: write
   MNTR_OBS_MTHD_TWO_NQ_END
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START 
   

   virtual function write(int id= -1, TR tr);
      this.tr = tr;
      -> cov_event;
   endfunction: write
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START


   virtual function void cov_sample(vmm_data tr1);
      $cast(tr,tr1);
      -> cov_event;
   endfunction: cov_sample
   MNTR_OBS_MTHD_FOUR_END

endclass: COV
   MNTR_OBS_MTHD_FOUR_START

   `vmm_notify_observer(COV, cov_sample)
   MNTR_OBS_MTHD_FOUR_END

`endif // COV__SV

