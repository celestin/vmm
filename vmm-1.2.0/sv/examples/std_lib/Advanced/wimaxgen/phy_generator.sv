/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

typedef class phy_generator;

class phy_generator_callbacks extends vmm_xactor_callbacks;
endclass

class phy_generator extends vmm_unit;
`vmm_typename(phy_generator)

 int unsigned      stop_after_n_frames = 1;
 phy_tb_config     phy_cfg;
 phy_frame         frame;

  function new(string inst, vmm_unit parent = null);
    super.new(get_typename(), inst, parent);
  endfunction

   virtual function void start_of_sim_ph();
     frame = phy_frame::create_instance(this, "Phy_fr0", `__FILE__, `__LINE__); 
     `vmm_note(log, $psprintf("%M - Phy frame type is %s", frame.get_typename()));
   endfunction

   virtual task config_dut_ph();
      $cast(phy_cfg, vmm_object::find_object_by_name("@%phy_cfg_inst_string_name"));
      if (phy_cfg == null) begin
        `vmm_error(log, `vmm_sformatf("null Config obtained for %s", this.get_object_hiername()));
        return;
      end

      phy_cfg.randomize();
      this.stop_after_n_frames = phy_cfg.num_of_frames;
      // pass the config to the frame instance after allocation
      frame.set_cfg(phy_cfg);
      `vmm_note(log, phy_cfg.psdisplay("env config_dut_ph"));
   endtask

  virtual task run_ph();
    fork
       // fork off main()
       this.main();
    join_none
  endtask

 virtual protected task main();
   int unsigned frames_id = 0;

   while (frames_id < stop_after_n_frames) begin
      frame.frame_index = frames_id;
      frame.randomize();
      `vmm_note(log, $psprintf("Frame %0d is built successfully", frames_id));
      `vmm_note(log, frame.psdisplay());
      frames_id++;
   end
 endtask

endclass

