/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class vmm_interop extends vmm_object;
   `vmm_typename(vmm_interop)

    typedef enum {SC_DRV = 0,
                  SV_DRV = 1
                  }interop_dir;
    local static vmm_interop vmm_sv_sc_interop        = new();
    static string phase_name;
    static int is_simulation = 0;
    static int is_timeline = 0;
    static vmm_interconnect_sv_sc snps_iconn;
    static vmm_timeline  top_test;
    static `VMM_LOG log;

    local function new(string name = "", string inst = "", vmm_object parent =null);
      super.new(parent, name);
      this.log = new("vmm_interop","SV-Class");
      snps_iconn = new("vmm_interconnect_sv_sc","snps_iconn");
    endfunction:new

   // to run run_phases in interop
   extern static task run_phase(interop_dir sv_sc, vmm_timeline tl = null);

   // to run run_tests in interop
   extern static task run_tests(interop_dir sv_sc);

endclass:vmm_interop

task vmm_interop::run_tests(interop_dir sv_sc);
   if(is_timeline == 1)
   begin
      `vmm_error(log,"SV-SC-Interop: Cannot call \"run_tests\" when \"run_phase\" is already called");
   end
   else
   begin
      is_simulation = 1;
      if(sv_sc == SV_DRV)
      begin
         vmm_simulation::set_sv2sc_interop();
         vmm_simulation::run_tests();
      end
      else
      begin
         snps_iconn.set_simulation();
         vmm_simulation::set_sc2sv_interop();
         snps_iconn.sync_sc_phase_with_sv();
      end
   end
endtask

task vmm_interop::run_phase(interop_dir sv_sc, vmm_timeline tl);
   if(is_simulation == 1)
   begin
      `vmm_error(log,"SV-SC-Interop: Cannot call \"run_phase\" when \"run_tests\" is already called");
   end
   else
   begin
      if(tl == null)
      begin
         `vmm_error(log,"Null object is passed for second argument \(vmm_timeline\) of run_phase method");
      end
      else
      begin
         is_timeline = 1;
         if(sv_sc == SV_DRV)
         begin
            tl.set_sv2sc_interop();
            tl.run_phase();
         end
         else
         begin
            snps_iconn.set_top_timeline(tl);
            tl.set_sc2sv_interop();
            snps_iconn.sync_sc_phase_with_sv();
         end
      end
   end
endtask

