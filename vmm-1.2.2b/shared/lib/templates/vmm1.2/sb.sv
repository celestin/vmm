//
// Template for VMM-compliant Data Stream Scoreboard
// <SB>         Name of vmm_sb_ds Scoreboard Class
// <TR>         Name of Transaction Descriptor

`ifndef SB__SV
`define SB__SV

 `include "vmm_sb.sv"
class SB extends vmm_sb_ds_typed#(TR,TR);

   `vmm_typename(SB)
   // DONE notification
   integer DONE;

   // Number of transaction count received by scoreboard
   int count = 0;

   // Constructor
   extern function new(string inst = "");
	extern virtual function bit compare(TR actual,
                                       TR expected);
  
   extern virtual function bit transform(input  TR in_pkt,
                                         output TR out_pkts[]);
   MNTR_OBS_MTHD_TWO_START
   extern virtual function void write_inp(int id=-1,TR tr);
   extern virtual function void write_exp(int id=-1,TR tr);
   MNTR_OBS_MTHD_TWO_END
   MNTR_OBS_MTHD_THREE_START
   extern virtual function void write_inp(int id=-1,TR tr);
   extern virtual function void write_exp(int id=-1,TR tr);
   MNTR_OBS_MTHD_THREE_END
   MNTR_OBS_MTHD_FOUR_START
   extern virtual function void sb_expect_in_order(vmm_data tr1);
   MNTR_OBS_MTHD_FOUR_END

endclass: SB


function SB::new(string inst = "");
   // Call the vmm_sb_ds base class
   super.new(inst);

   // Configure DONE notification to be ON/OFF
   DONE = notify.configure(-1, vmm_notify::ON_OFF);
endfunction: new


function bit SB::compare(TR actual,TR expected);
  super.compare(actual,expected);
  //This scoreboard performs the basic comparison using the TR.compare, however user can add
  //further logic here if required.   
endfunction: compare 


function bit SB::transform(input  TR in_pkt,
                           output TR out_pkts[]);
   // ToDo: Declare transaction instance and form out_pkts

   out_pkts = new [1];
   out_pkts[0] = in_pkt;
endfunction: transform
MNTR_OBS_MTHD_TWO_START


//Write_inp method of the vmm_sb_ds will get executed when the write method of the bound analysis port is called
function void SB::write_inp(int id=-1,TR tr);
   this.insert(tr,.exp_stream_id(1));

endfunction : write_inp


//Write_exp method of the vmm_sb_ds will get executed when the write method of the bound analysis port is called
function void SB::write_exp(int id=-1,TR tr);
   this.expect_in_order(tr,.exp_stream_id(1));

endfunction : write_exp
MNTR_OBS_MTHD_TWO_END
MNTR_OBS_MTHD_THREE_START


//Write_inp method of the vmm_sb_ds will get executed when the write method of the bound analysis port is called
function void SB::write_inp(int id=-1,TR tr);
   this.insert(tr,.exp_stream_id(1));

endfunction : write_inp


//Write_exp method of the vmm_sb_ds will get executed when the write method of the bound analysis port is called
function void SB::write_exp(int id=-1,TR tr);
   this.expect_in_order(tr,.exp_stream_id(1));

endfunction : write_exp
MNTR_OBS_MTHD_THREE_END
MNTR_OBS_MTHD_FOUR_START


function void SB::sb_expect_in_order(vmm_data tr1);
   TR tr;
   $cast(tr,tr1);
   this.expect_in_order(tr);
endfunction: sb_expect_in_order

`vmm_notify_observer(SB, sb_expect_in_order)
MNTR_OBS_MTHD_FOUR_END

`endif // SB__SV
