class memsys_scenario extends memsys_trans_scenario;
  int SCN_KIND = this.define_scenario("MEMSYS_SCENARIO", 2);

  constraint cst_memsys_scenario {
    repeated == 0;
    length == 2;
  }

  virtual function vmm_data allocate();
       memsys_scenario scn = new();
       return scn;
  endfunction

  virtual function vmm_data copy(vmm_data to = null);
     memsys_scenario scn = new();
     scn.SCN_KIND = this.SCN_KIND;
     copy = super.copy(scn);
  endfunction

`vmm_class_factory(memsys_scenario)
endclass



