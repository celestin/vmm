//
// Template for VMM-compliant Data Stream Scoreboard Callbacks
// <SB_CB>      Name of VMM Scoreboard Callback Class
// <SB>         Name of VMM Scoreboard Class
// <XACT>       Name of Master/Slave transactor class
// <TR>         Name of transaction descriptor class
//

`ifndef SB_CB__SV
`define SB_CB__SV

typedef class XACT;
typedef class SB;

//ToDo: Callback methods of this class are made only with respect to physical level components(driver/monitor)
class XACT_sb_callbacks extends XACT_callbacks;

   SB sb;

   function new(SB sb);
      this.sb = sb;
      // ToDo: Add relevant code  
   endfunction: new

   // ToDo: Add additional relevant callbacks
   // ToDo: Use a task if callbacks can be blocking
   FULL_DUPLEX_FNC_BFM_START
   // Called after a transaction has been executed
   virtual task post_in_trans(XACT xactor,
                              TR tr);
      SCB_INT_COMMON_CODE_START
      sb.insert(tr);  
      SCB_INT_COMMON_CODE_END
      // ToDo: Add relevant code  
   endtask: post_in_trans
   FULL_DUPLEX_FNC_BFM_END

   FULL_DUPLEX_PHY_BFM_START
   // Called after a transaction has been executed
   virtual task post_ex_trans(XACT xactor,
                              TR tr);
      SCB_INT_COMMON_CODE_START
      sb.insert(tr);  
      SCB_INT_COMMON_CODE_END
      // ToDo: Add relevant code  
   endtask: post_ex_trans
   FULL_DUPLEX_PHY_BFM_END

endclass: XACT_sb_callbacks

`endif // SB_CB__SV
