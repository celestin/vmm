//
// Template for VMM-compliant Monitor scoreboard callbacks
// <SB>         Name of VMM Scoreboard Class
// <MON>        Name of Monitor transactor class
// <TR>         Name of transaction descriptor class
// [filename]   MON_sb_cb

`ifndef MON_sb_cb__SV
`define MON_sb_cb__SV


typedef class MON;

class MON_sb_cb extends MON_callbacks;

   SB sb;

   function new(SB sb);
      this.sb = sb;
   endfunction: new

   // ToDo: Add additional relevant callbacks
   // ToDo: Use "task" if callbacks can be blocking

   virtual function void pre_trans (MON xactor,
                                    TR tr);
      // ToDo: Add relevant code  

   endfunction: pre_trans


   virtual function void post_trans (MON xactor,
                                     TR tr);
      sb.expect_in_order(tr);   
      // ToDo: Add relevant code if required 

   endfunction: post_trans

endclass: MON_sb_cb

`endif // MON_sb_cb__SV
