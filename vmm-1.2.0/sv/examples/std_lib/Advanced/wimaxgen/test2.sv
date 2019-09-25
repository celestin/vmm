/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

// Shows how to create a new factory with specific constraints
class my_frame extends phy_frame;
  `vmm_typename(my_frame)
   constraint cst_user {
      num_of_super_zones == 2;

      foreach (super_zone_lengths[i]) {
        super_zone_lengths[i] == 12; 
      }
   
      foreach (super_zone_list[i]) {
        (i==0) -> super_zone_list[i].super_zone_direction == phy_super_zone::RX_SUPER_ZONE;
        (i==1) -> super_zone_list[i].super_zone_direction == phy_super_zone::TX_SUPER_ZONE;
        (i==0) -> super_zone_list[i].super_zone_mode == phy_super_zone::DOWNLINK;
        (i==1) -> super_zone_list[i].super_zone_mode == phy_super_zone::UPLINK;
      }
   }
   
   function new(phy_tb_config phy_cfg = null);
      super.new(phy_cfg);
   endfunction

   virtual function vmm_data allocate();
      my_frame fr = new(this.phy_cfg);
      return fr;
   endfunction

   virtual function vmm_data copy(vmm_data to=null);
      my_frame fr = new(this.phy_cfg);
      return fr;
   endfunction

   `vmm_class_factory(my_frame)
endclass

// New test with constraints
class test2 extends vmm_test;
  `vmm_typename(test2)
    
  function new(string name);
     super.new(name);
  endfunction

  virtual function void start_of_sim_ph();
     `vmm_note(log, $psprintf("Starting %s - %M", this.get_typename())); 
     // Sneak in new factory everywhere in the env
     phy_frame::override_with_new("@%*", my_frame::this_type, log);
  endfunction
endclass
