/***************************************************************************
 *******************************************************************************
 * gets the input object from gen and passes to DUT (BFM)
 *******************************************************************************
 */

`ifndef _FPU_MASTER_SV_
`define _FPU_MASTER_SV_

typedef class fpu_trans;
typedef class fpu_master;
typedef class fpu_trans_channel;

class fpu_master_callbacks extends vmm_xactor_callbacks ;

    // Called before a transaction is executed
    virtual task pre_trans(fpu_master master,
            fpu_trans  tr,
            ref bit drop);
    endtask: pre_trans

    // Called after a transaction has been executed
    virtual task post_trans(fpu_master master,
            fpu_trans  tr);
    endtask: post_trans

endclass: fpu_master_callbacks


class fpu_master extends vmm_xactor ;

    // Input vmm_channel: this is where transactions
    // to be sent stand
    fpu_trans_channel in_trans;

    // Event ID notifying when a transaction has been completed
    static int TRANS_DONE;

    // Interface to FPU HDL signals
    // ToDo: Waiting for Bug fix to declare as local modport
    virtual fpu_i.STB iport;

    // FPU configs
    local fpu_cfg icfg;

    // Constructor
    function new(string        inst,
             int               stream_id,
             virtual fpu_i.STB     iport,
             fpu_cfg           icfg     = null,
             fpu_trans_channel in_trans = null);
	super.new("FPU Master", inst, stream_id);
	this.iport = iport;

	if (icfg==null) begin
	    icfg = new;
	end 
	this.icfg = icfg;

	if (in_trans==null) begin
	    in_trans = new("FPU Master Input Channel", inst);
	end
	this.in_trans = in_trans;

	this.TRANS_DONE = this.notify.configure(.sync(vmm_notify::ON_OFF ));
    endfunction: new

    // From vmm_xactor
    virtual function void reset_xactor(reset_e rst_type = 0);
	super.reset_xactor(rst_type);

	this.in_trans.flush();
	//ToDo: what port values on reset !? spec is incomplete output seems "X"
    endfunction: reset_xactor

    protected virtual task main();
	fpu_trans tr;

	fork
	    super.main();
	join_none

	while(1) begin
	    bit drop = 0;
	    int op_int;
	    int rmode_int;
	    // Get a transaction from the mailbox
	    // and cast to a fpu_trans
       this.wait_if_stopped_or_empty(this.in_trans);
       this.in_trans.get(tr);

	    `vmm_callback(fpu_master_callbacks, pre_trans(this, tr, drop));
	    if (drop) begin
		if (this.log.start_msg(vmm_log::DEBUG_TYP, vmm_log::DEBUG_SEV)) begin
		    if (this.log.text("Dropping transaction...")) begin
			void'(this.log.text());
			tr.display("   ");
		    end
		    void'(this.log.text());
		end
		continue;
	    end

	    if (this.log.start_msg(vmm_log::DEBUG_TYP, vmm_log::TRACE_SEV)) begin
		if (this.log.text("Starting transaction...")) begin
		    void'(this.log.text());
		    tr.display("   ");
		end
		void'(this.log.text());
	    end

	    tr.notify.indicate(vmm_data::STARTED);

	    // Decide what to do now with the incoming
	    // transaction
            @(this.iport.cb); //equivalent to ##1, as default clking is iport.STB.cb
	    op_int = tr.op;
	    rmode_int = tr.rmode;
            //ToDo: may need to make next 4 drives async
	    this.iport.cb.fpu_op <= op_int; 
	    this.iport.cb.rmode <= rmode_int;
	    this.iport.cb.opa <= {tr.opa.sign, tr.opa.exponent, tr.opa.significand};
	    this.iport.cb.opb <= {tr.opb.sign, tr.opb.exponent, tr.opb.significand};
	    `vmm_callback(fpu_master_callbacks, post_trans(this, tr));

	    this.notify.indicate(this.TRANS_DONE, tr);
	    tr.notify.indicate(vmm_data::ENDED);
	end
    endtask: main

endclass: fpu_master


`endif
