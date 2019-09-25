//
// Template for VMM-compliant Monitor to Coverage Connector Callbacks
//
// <COV>        Name of Coverage Class
// <MON>        Name of Monitor transactor class
// <TR>         Name of transaction descriptor class
//  [filename]   MON_2cov_connect


`ifndef MON_2cov_connect
`define MON_2cov_connect


class MON_2cov_connect extends MON_callbacks;

   COV cov;

   function new(COV cov);
      this.cov = cov;
   endfunction: new

   // ToDo: Use "function" if callbacks cant be blocking
   
   // Callback method post_cb_trans can be used for coverage
   virtual task post_cb_trans(MON xactor,
                              TR tr);
      cov.tr = tr; 
      -> cov.cov_event;
    
   endtask: post_cb_trans

endclass: MON_2cov_connect

`endif // MON_2cov_connect
