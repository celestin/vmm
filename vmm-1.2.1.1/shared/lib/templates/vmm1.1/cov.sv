//
// Template for VMM-compliant Coverage Class
// <COV>        Name of Coverage class
// <TR>         Name of Transaction descriptor class
//

`ifndef COV__SV
`define COV__SV

class COV;
   event cov_event;
   TR tr;

   covergroup cg_trans @(cov_event);
      coverpoint tr.kind;
      // ToDo: Add required coverpoints, coverbins
   endgroup: cg_trans

   function new();
      cg_trans = new;
   endfunction: new

endclass: COV

`endif // COV__SV
