//
// Template for VMM-compliant Data Stream Scoreboard
// <SB>         Name of vmm_sb_ds Scoreboard Class
// <TR>         Name of transaction descriptor class

`ifndef SB__SV
`define SB__SV

// ToDo: Add additional required `include directives
`include "vmm_sb.sv"
class SB extends vmm_sb_ds;

   // Iterator class instance of type vmm_sb_ds_iter
   vmm_sb_ds_iter sb_iter;

   // DONE notification
   integer DONE;

   // Number of transaction count received by scoreboard
   int count = 0;

   // Constructor
   extern function new(string inst = "");
	extern virtual function bit compare(vmm_data actual,
                                       vmm_data expected);
   extern virtual function bit transform(input  vmm_data in_pkt,
                                         output vmm_data out_pkts[]);

endclass: SB


function SB::new(string inst = "");

   // Call the vmm_sb_ds base class
   super.new(inst);

   sb_iter  = this.new_sb_iter(0,0);

   // Configure DONE notification to be ON/OFF
   DONE = notify.configure(-1, vmm_notify::ON_OFF);

endfunction: new

function bit SB::compare(vmm_data actual,vmm_data expected);
  super.compare(actual,expected);
  //This scoreboard performs the basic comparison using the TR.compare, however user can add
  //further logic here if required.   
endfunction: compare 

function bit SB::transform(input  vmm_data in_pkt,
                           output vmm_data out_pkts[]);

   // ToDo: Declare transaction instance and form out_pkts
   
   // Code for reference(assuming pkt_t as transaction descriptor)
   // pkt_t p, q;
   // $cast(p, in_pkt);
   out_pkts = new [1];
   out_pkts[0] = in_pkt;

endfunction: transform

`endif // SB__SV
