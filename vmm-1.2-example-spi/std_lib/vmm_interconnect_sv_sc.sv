/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class vmm_interconnect_sv_sc extends vmm_object;
   `vmm_typename(vmm_interconnect_sv_sc)

    string phase_name;
    int is_simulation;
    vmm_timeline  top_test;

    function new(string name = "", string inst = "", vmm_object parent =null);
      super.new(parent, name);
      this.is_simulation = 0;
    endfunction:new

   // Set the systemc vmm_timeline for interconnect class
   extern virtual function set_top_timeline( vmm_timeline top_timeline);

   // Set the simulation for sc_sv flow
   extern virtual task set_simulation();

   // Thread process to interact with SC Phases
   extern virtual task sync_sc_phase_with_sv();

endclass:vmm_interconnect_sv_sc

function vmm_interconnect_sv_sc::set_top_timeline(vmm_timeline top_timeline);
     this.top_test = top_timeline;
     //this.sync_sc_phase_with_sv();
endfunction: set_top_timeline

task vmm_interconnect_sv_sc::set_simulation();
     vmm_simulation::execute_pre_test("$");
     this.top_test = vmm_simulation::get_top_timeline();
     this.is_simulation = 1;
     //this.sync_sc_phase_with_sv();
endtask

task vmm_interconnect_sv_sc::sync_sc_phase_with_sv();
        while(1) begin // [[ 
            vmm_sc2sv_sync_phase(this.phase_name);
            if(this.is_simulation == 1)
            begin
               if(this.phase_name == "final")
                  this.top_test = vmm_simulation::get_post_timeline();
            end
            top_test.run_phase(this.phase_name);
            vmm_sc2sv_sync_phase_over();
        end // ]]
endtask: sync_sc_phase_with_sv
