/***************************************************************************
 *******************************************************************************
 *
 * Basic Transaction Verification Module aimed at
 * creating input stimulus for FPU
 *
 *******************************************************************************
 */

`ifndef _FPU_GEN_SV
`define _FPU_GEN_SV

typedef class fpu_gen;
typedef class fpu_scenario;

class fpu_gen_callbacks extends vmm_xactor_callbacks;

    // Callback method called after each scenario generated
    virtual task post_scenario_gen(fpu_gen      gen,
                                   fpu_scenario scenario);
    endtask: post_scenario_gen

    // Callback method used to modify transaction descriptor
    // prior to sending over
    virtual task pre_tr_fwd(fpu_gen   gen,
                            fpu_trans tr,
                            ref bit   drop);
    endtask: pre_tr_fwd
endclass: fpu_gen_callbacks


class fpu_scenario;
    // Factory instance used to build the scenario items
    fpu_trans randomized_tr;

    int stream_id;
    int scenario_id;

    static bit [31:0] NULL = 0;

    rand bit [31:0] kind;
    rand bit [31:0] length;
    rand fpu_trans items[$];

    local int next_idx;

    constraint fpu_scenario_basic {
        solve kind before length;
        //ToDo: function in constraint not yet supported
        //items.size == length;

        if (kind == NULL) length == 1;
    }

    constraint valid_scenarios {
        kind == NULL;
    }

    function new() ;
        this.randomized_tr = new;
    endfunction: new

    protected task resize_items(int n) ;
        while (this.items.size() < n) begin
            fpu_trans tr;

            this.randomized_tr.data_id = this.items.size();
            $cast(tr, this.randomized_tr.copy());
            this.items.push_back(tr);
        end
    endtask: resize_items

    function void pre_randomize();
        // Flush the scenario list because they
        // have been forwarded to the output channel.
        // We need new instances to avoid modifying the
        // same ones from the previous scenario...
        this.items.delete();

        // Pre-allocate enough scenario items
        // for the maximum-length scenario
        this.randomized_tr.stream_id   = this.stream_id;
        this.randomized_tr.scenario_id = this.scenario_id;
        this.resize_items(1);

        this.next_idx = 0;
    endfunction: pre_randomize

    function void post_randomize();
        // Trim the items because the solver only solves
        // for the constrained size, not the actual size!
        while (this.items.size() > this.length) begin
            void'(this.items.pop_back());
        end
    endfunction: post_randomize

    virtual function fpu_trans next_item();
        if (next_idx >= this.items.size()) begin
            next_item = null;
        end else begin
            next_item = this.items[next_idx++];
        end
    endfunction: next_item
endclass: fpu_scenario


//ToDo: use scenario generator macro
class fpu_gen extends vmm_xactor ;

    int scenario_id;

    // Blueprint (factory) instance
    fpu_scenario randomized_sc;

    // Output vmm_channel: this is where transactions
    // to be sent end up
    fpu_trans_channel out_trans;

    // Stop after having generated the specified number of scenarios
    // 0 == never stop (default)
    int stop_after_n_scenarios;

    function new(string            inst,
                 int               stream_id,
                 fpu_trans_channel out_trans = null) ;

        super.new("FPU input Generator", inst);

        if (out_trans == null) begin
            out_trans = new({this.log.get_name(), " Output Channel"}, 
                            inst);
        end
        this.out_trans = out_trans;

        this.randomized_sc = new;
        this.scenario_id = 0;

        this.stop_after_n_scenarios = 0;
    endfunction: new

    // Method aimed at generating transactions
    // (derived from the vmm_xactor)
    protected virtual task main();
	fork
	    super.main();
	join_none

        while (1) begin
            fpu_trans tr;
            bit drop = 0;

            if (this.stop_after_n_scenarios > 0 &&
                    this.scenario_id >= this.stop_after_n_scenarios) begin
                this.stop_xactor();
            end
            super.wait_if_stopped();

            this.randomized_sc.stream_id   = this.stream_id;
            this.randomized_sc.scenario_id = this.scenario_id++;

            // Randomize the scenario
            void'(this.randomized_sc.randomize());

            // Report the scenario via a callback
            `vmm_callback(fpu_gen_callbacks,
                    post_scenario_gen(this, this.randomized_sc));

            // Forward the scenario to the output channel
            for (tr = this.randomized_sc.next_item();
                 tr != null;
                 tr = this.randomized_sc.next_item()) begin

                // Give a chance to modify object
                `vmm_callback(fpu_gen_callbacks,
                        pre_tr_fwd(this, tr, drop));
                if (!drop) begin
                    out_trans.put(tr);
                    tr.notify.wait_for(vmm_data::ENDED);
                end
            end
        end
    endtask: main

    // Reset the transaction generator
    virtual function void reset_xactor(reset_e rst_type = 0);
	super.reset_xactor(rst_type);
	this.scenario_id = 0;
    endfunction: reset_xactor

endclass: fpu_gen


`endif
