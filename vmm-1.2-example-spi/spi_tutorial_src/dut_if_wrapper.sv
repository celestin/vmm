//////////////////////////////////////////////////////////////////////////////
//
//  DDDDD   OOO  UU UU LL    OOO   SSS
//  DD  DD OO OO UU UU LL   OO OO SS  S
//  DD  DD OO OO UU UU LL   OO OO  SS
//  DD  DD OO OO UU UU LL   OO OO   SS
//  DD  DD OO OO UU UU LL   OO OO S  SS
//  DDDDD   OOO   UUU  LLLL  OOO   SSS
//
//  Doulos
//
//  Filename: dut_if_wrapper.sv
//  Date: 5 Nov 2009
//  Author: Doug Smith
//  Description:  Wrapper to contain the virtual interface.
//
//////////////////////////////////////////////////////////////////////////////

`ifndef DUT_IF_WRAPPER_SV
`define DUT_IF_WRAPPER_SV

class dut_if_wrapper extends vmm_object;

   virtual dut_intf	dut_if;

   function new( string name, virtual dut_intf dut_if );
	super.new( null, name );
	this.dut_if = dut_if;
   endfunction : new

endclass

`endif	// DUT_IF_WRAPPER_SV
