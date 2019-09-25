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

// Shows how to create a new factory with specific constraints
class my_frame extends phy_frame;
  `vmm_typename(my_frame)
   constraint cst_user {
      num_of_super_zones == 2;

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
