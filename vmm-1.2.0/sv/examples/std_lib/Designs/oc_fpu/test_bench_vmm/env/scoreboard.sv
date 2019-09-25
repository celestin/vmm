/***************************************************************************
 *******************************************************************************
 *
 * Scoreboard module used to verify the
 * incoming and outgoing transactions correctness
 *
 *******************************************************************************
 */

`ifndef _SCOREBOARD_SV_
`define _SCOREBOARD_SV_

class scoreboard ;
    vmm_log log;

    test_cfg cfg;
    static fpu_result rsltQ[$];

    // Constructor
    function new(test_cfg cfg) ;
        int i;

        this.log = new("Scoreboard", "singleton");
        this.cfg = cfg;
        repeat(5) begin
            fpu_result rslt_temp; 
            rslt_temp = new;
            this.rsltQ.push_back(rslt_temp);
        end
    endfunction: new

    //ToDo: implement using DPI to demo DPI, or using
    //  floating point calculation capabilities of SV 
    virtual task calculate_result(fpu_trans tr);

	fpu_result rslt_temp; 
	bit [31:0] zero_val;
	integer opa_significand_int;
	integer opb_significand_int;
	bit [24:0] sum_significand;
	rslt_temp = new;
	//`vmm_note(this.log,"TBD");
	rslt_temp.out = 0;
	rslt_temp.zero = 0;
	rslt_temp.snan = 0;
	rslt_temp.qnan = 0;
	rslt_temp.inf = 0;
	rslt_temp.ine = 0;
	rslt_temp.div_by_zero = 0;
        //ToDo: fix class local enum with wa.
	//if((tr.op == fpu_trans::ADD)||(tr.op == fpu_trans::SUB)) begin
	if((tr.op == ADD)||(tr.op == SUB)) begin
	    //if(tr.op == fpu_trans::SUB) begin
	    if(tr.op == SUB) begin
		tr.opb.sign = ~tr.opb.sign;
	    end
	    if((tr.opa.significand == 0) && (tr.opa.exponent == 0)) begin
		rslt_temp.out = {tr.opb.sign, tr.opb.exponent, tr.opb.significand};
		zero_val = {1'b0, tr.opb.exponent, tr.opb.significand };
		if(zero_val == 0) begin
		    rslt_temp.zero = 1;
		end
		this.rsltQ.push_back(rslt_temp);
		return;
	    end else if((tr.opb.significand == 0) && (tr.opb.exponent == 0)) begin
		rslt_temp.out = {tr.opa.sign, tr.opa.exponent, tr.opa.significand};
		zero_val = {1'b0, tr.opa.exponent, tr.opa.significand };
		if(zero_val == 0) begin
		    rslt_temp.zero = 1;
		end
		this.rsltQ.push_back(rslt_temp);
		return;
	    end 

	    if(tr.opa.exponent != tr.opb.exponent) begin
		if(tr.opa.exponent < tr.opb.exponent)  begin
		    tr.opa.significand = (tr.opa.significand >> (tr.opb.exponent - tr.opa.exponent));
		    tr.opa.exponent = tr.opb.exponent;
		    if(tr.opa.significand == 0) begin
			rslt_temp.out = {tr.opb.sign, tr.opb.exponent, tr.opb.significand};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end

		end else if(tr.opb.exponent < tr.opa.exponent)  begin
		    tr.opb.significand = (tr.opb.significand >> (tr.opa.exponent - tr.opb.exponent));
		    tr.opb.exponent = tr.opa.exponent;
		    if(tr.opb.significand == 0) begin
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, tr.opa.significand};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end
		end
	    end


	    //ToDo: fix with class local enum
            //if(tr.op == fpu_trans::ADD) begin
	    if(tr.op == ADD) begin
		if((tr.opa.sign ^ tr.opb.sign) == 1)  begin
		    sum_significand = tr.opa.significand + (~tr.opb.significand) + 1'b1 ;
		    if(sum_significand[24] == 1) begin
			if(sum_significand[23:0] == 0) begin
			    rslt_temp.zero = 1;
			    this.rsltQ.push_back(rslt_temp);
			    return;
			end else  begin
			    while(sum_significand[23] == 0) begin
				sum_significand = (sum_significand << 1);
				tr.opa.exponent =  tr.opa.exponent + 1;
			    end
			    rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			    this.rsltQ.push_back(rslt_temp);
			    return;
			end
		    end else if(sum_significand[24] == 0)  begin
			sum_significand = (~sum_significand) + 1'b1 ;
			tr.opa.sign = ~tr.opa.sign;
			while(sum_significand[23] == 0) begin
			    sum_significand = (sum_significand << 1);
			    tr.opa.exponent =  tr.opa.exponent + 1;
			end
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end
		end else  begin
		    sum_significand = tr.opa.significand + tr.opb.significand;
		    if(sum_significand[24] == 1) begin
			sum_significand = (sum_significand >> 1);
			tr.opa.exponent =  tr.opa.exponent + 1;
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end else  begin
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end
		end

	    //ToDo: fix with class local enum
            //end else if(tr.op == fpu_trans::SUB) begin
	    end else if(tr.op == SUB) begin
		if((tr.opa.sign ^ tr.opb.sign) == 0)  begin
		    sum_significand = tr.opa.significand + (~tr.opb.significand) + 1'b1 ;
		    if(sum_significand[24] == 1) begin
			if(sum_significand[23:0] == 0) begin
			    rslt_temp.zero = 1;
			    this.rsltQ.push_back(rslt_temp);
			    return;
			end else  begin
			    while(sum_significand[23] == 0) begin
				sum_significand = (sum_significand << 1);
				tr.opa.exponent =  tr.opa.exponent + 1;
			    end
			    rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			    this.rsltQ.push_back(rslt_temp);
			    return;
			end
		    end else if(sum_significand[24] == 0)  begin
			sum_significand = (~sum_significand) + 1'b1 ;
			tr.opa.sign = ~tr.opa.sign;
			while(sum_significand[23] == 0) begin
			    sum_significand = (sum_significand << 1);
			    tr.opa.exponent =  tr.opa.exponent + 1;
			end
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end
		end else  begin
		    sum_significand = tr.opa.significand + tr.opb.significand;
		    if(sum_significand[24] == 1) begin
			sum_significand = sum_significand >> 1;
			tr.opa.exponent =  tr.opa.exponent + 1;
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end else  begin
			rslt_temp.out = {tr.opa.sign, tr.opa.exponent, sum_significand[23:0]};
			this.rsltQ.push_back(rslt_temp);
			return;
		    end
		end
	    end
	end

    endtask: calculate_result


    virtual task compare_result(fpu_result rslt);
	fpu_result temp_rslt;
	bit compare;
	string diff;
	if(this.rsltQ.size() > 0) begin
	    temp_rslt = rsltQ.pop_front();
	    compare = temp_rslt.compare(rslt,diff);
	    if(compare == 0) begin
		`vmm_warning(this.log,$psprintf("%s",diff));
	    end
	end else  begin
	    `vmm_warning(this.log,"Objects didn't put into the Q");
	end
		    
    endtask: compare_result

endclass: scoreboard

`endif
