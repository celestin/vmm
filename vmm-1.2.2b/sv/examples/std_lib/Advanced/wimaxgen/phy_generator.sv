//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

typedef class phy_generator;

class phy_generator_callbacks extends vmm_xactor_callbacks;
endclass

class phy_generator extends vmm_group;
`vmm_typename(phy_generator)

 int unsigned      stop_after_n_frames = 1;
 phy_tb_config     phy_cfg;
 phy_frame         frame;

  function new(string inst, vmm_group parent = null);
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

