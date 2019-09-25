/*
*******************************************************************************
*
* Basic Transaction Monitoring Module aimed at
* creating monitor() transaction.
*
* This transaction constantly watches the FPU outputs,
* pushing the result into the scoreboard thru callback 
*
*******************************************************************************
*/

`ifndef _FPU_MON_SV_ 
`define _FPU_MON_SV_ 

class fpu_result extends vmm_data ;

    // Data Logger
    static vmm_log log = new("fpu_result", "class");

    rand bit [31:0] out;
    rand bit zero;
    rand bit snan;
    rand bit qnan;
    rand bit inf;
    rand bit ine;
    rand bit div_by_zero;

    function new();
	super.new(this.log);
    endfunction: new

    virtual function string psdisplay(string prefix = "");
        string result;
	if( this.zero == 1)
	    result = $psprintf("%s out is Zero", prefix);
	else if( this.snan == 1)
	    result = $psprintf("%s out is SNAN", prefix);
	else if(  this.qnan == 1)
	    result = $psprintf("%s out is QNAN", prefix);
	else if( this.inf == 1)
	    result = $psprintf("%s out is INF", prefix);
	else       
	    result = $psprintf("%s out = %x", prefix, this.out);
       
	if(this.ine == 1) begin
	    result = {result, ". The result is INEXACT"};
        end

        return result;
    endfunction: psdisplay

    virtual function vmm_data allocate();
	fpu_result rslt = new;
	allocate = rslt;
    endfunction: allocate


    virtual function vmm_data copy(vmm_data cpy = null);
	fpu_result to = null;

	if (cpy == null) begin
	    to = new;
	end else if (!$cast(to, cpy)) begin
	    `vmm_fatal(this.log, "Attempting to copy to a non-fpu_result instance");
	    copy = null;
	    return;
	end

	super.copy_data(to);

	to.out = this.out;
	to.zero = this.zero;
	to.snan = this.snan;
	to.qnan = this.qnan;
	to.inf = this.inf;
	to.ine = this.ine;
	to.div_by_zero = this.div_by_zero;

	copy = to;
    endfunction: copy


    virtual function bit compare(vmm_data   to,
				 output string diff,
				 input int kind = -1);
	fpu_result rslt;
	diff = "";
	if (!$cast(rslt, to)) begin
	    diff = "Not a fpu_result instance";
	    compare = 0;
	    return;
	end

	compare = 1;

	if (this.out !== rslt.out) begin
	    diff = $psprintf("Out is different %x != %x", this.out, rslt.out);
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if (this.zero !== rslt.zero) begin
	    diff = $psprintf("zero is different");
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if (this.snan !== rslt.snan) begin
	    diff = $psprintf("snan is different");
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if (this.qnan !== rslt.qnan) begin
	    diff = $psprintf("qnan is different");
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if (this.inf !== rslt.inf) begin
	    diff = $psprintf("inf is different");
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if (this.div_by_zero !== rslt.div_by_zero) begin
	    diff = $psprintf("div_by_zero is different");
	    //`vmm_warning(this.log,"Comparison failed ");
	    compare = 0;
	end

	if(compare == 1) begin
	    `vmm_note(this.log,$psprintf("***Comparison success with outs %x == %x", this.out, rslt.out));
	end

    endfunction: compare

    virtual function int unsigned byte_size(int kind = -1);
	byte_size = 0;
    endfunction

    virtual function int unsigned byte_pack(ref logic [7:0] bytes[],
				   input int unsigned offset = 0,
				   input int kind   = -1);
	byte_pack = 0;
    endfunction: byte_pack

    virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[],
				     input int unsigned offset = 0,
				     int len   = -1,
				     int kind   = -1);
	byte_unpack = 0;
    endfunction: byte_unpack

endclass: fpu_result

// Declare a specific vmm_channel of fpu_result
`vmm_channel(fpu_result)

typedef class fpu_mon;

class fpu_mon_callbacks extends vmm_xactor_callbacks;
    // Called after a new transaction has been observed
    virtual task post_mon(fpu_mon    mon,
                          fpu_result rslt,
                          ref bit    drop);
    endtask: post_mon
endclass: fpu_mon_callbacks


class fpu_mon extends vmm_xactor;

    // Factory instance for transaction descriptors
    fpu_result allocated_rslt;

    // Interface to FPU HDL signals
    virtual fpu_i.STB iport;

    // Output channel of observed transactions
    fpu_result_channel out_chan;

    // Are transactions put into the output channel?
    local bit is_sink;

    // Constructor
    function new(string               inst,
                 int                  stream_id,
                 virtual fpu_i.STB        iport,
                 fpu_result_channel   out_chan = null,
                 bit                  is_sink  = 0) ;
	super.new("FPU Mon", inst, stream_id);

	this.allocated_rslt = new;

	this.iport = iport;

	if (out_chan == null) begin
	    out_chan = new({this.log.get_name(), " Output Channel"}, 
                           inst);
	end
	this.out_chan = out_chan;
	this.is_sink = is_sink;

	// Make sure output channel will never block
	out_chan.reconfigure(65535);
    endfunction: new 

    // From vmm_xactor
    virtual function void reset_xactor(reset_e rst_type = 0);
	super.reset_xactor(rst_type);
	this.out_chan.flush();
    endfunction: reset_xactor

    // From vmm_xactor
    virtual task main();
	fork
	    super.main();
	join_none

        while (1) begin
            fpu_result rslt;
            bit drop = is_sink;

            super.wait_if_stopped();

            //##1;
            @(this.iport.cb); 

            $cast(rslt, this.allocated_rslt.allocate());
            this.monitor(rslt);

            if (this.log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV)) begin
                if (this.log.text("Observed result...")) begin
                    void'(this.log.text());
                    rslt.display("   ");
                end
                this.log.end_msg();
            end

            `vmm_callback(fpu_mon_callbacks,
                    post_mon(this, rslt, drop));

            if (!drop) begin
                if (this.log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV)) begin
                    if (this.log.text("Forwarding result...")) begin
                        void'(this.log.text());
                        rslt.display("   ");
                    end
                    this.log.end_msg();
                end

                fork
                   `vmm_warning(this.log, "Output channel is full. Monitoring temporarily suspended");
                join_none
                this.out_chan.put(rslt);
                disable fork;
            end
        end
    endtask: main

    // Monitors the bus and returns whenver a new transaction
    // has been observed
    local task monitor(ref fpu_result rslt);
	rslt.out      = this.iport.cb.out;
	rslt.zero     = this.iport.cb.zero;
	rslt.snan     = this.iport.cb.snan;
	rslt.qnan     = this.iport.cb.qnan;
	rslt.inf      = this.iport.cb.inf;
	rslt.ine      = this.iport.cb.ine;
	rslt.div_by_zero = this.iport.cb.div_by_zero;
    endtask: monitor

endclass: fpu_mon

`endif
