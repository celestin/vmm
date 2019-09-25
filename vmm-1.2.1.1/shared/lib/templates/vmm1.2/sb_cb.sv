//
// Template for VMM-compliant Data Stream Scoreboard Callbacks
// <SB_CB>      Name of VMM Scoreboard Callback Class
// <SB>         Name of VMM Scoreboard Class
// <XACT>       Name of Master/Slave transactor class
// <TR>         Name of transaction descriptor class
//

`ifndef XACT_sb_cb__SV
`define XACT_sb_cb__SV

typedef class XACT;
typedef class SB;

//ToDo: Callback methods of this class are made only with respect to physical level components(driver/monitor)
//For functional level components, User need to change the arguments of these functions.
class XACT_sb_cb extends XACT_callbacks;

   `vmm_typename(XACT_sb_cb)
   vmm_tlm_analysis_port #(XACT_sb_cb,TR) bfm_analysis_port;  //Instance of analysis port to pass data to the scoreboard

   function new();
      bfm_analysis_port= new(this,"BFM-SB analysis port"); 
      // ToDo: Add relevant code  
   endfunction: new

   // ToDo: Add additional relevant callbacks
   // ToDo: Use a task if callbacks can be blocking
   FULL_DUPLEX_FNC_BFM_START
   // Called after a transaction has been executed
   virtual task post_in_trans(XACT xactor,
                              TR tr);
      bfm_analysis_port.write(tr);
      // ToDo: Add relevant code  
   endtask: post_in_trans
   FULL_DUPLEX_FNC_BFM_END

   FULL_DUPLEX_PHY_BFM_START
   // Called after a transaction has been executed
   virtual task post_ex_trans(XACT xactor,
                              TR tr);
      bfm_analysis_port.write(tr);
      // ToDo: Add relevant code  
   endtask: post_ex_trans
   FULL_DUPLEX_PHY_BFM_END
  
 
endclass: XACT_sb_cb

`endif // SB_CB__SV
