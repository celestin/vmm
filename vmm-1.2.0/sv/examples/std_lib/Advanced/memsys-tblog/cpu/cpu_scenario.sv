class cpu_scenario extends cpu_trans_scenario;
  
  constraint cst_cpu_scenario {
    repeated == 0;
    length == 2;
  }

  function new();
    super.new();
    this.define_scenario("CPU SCENARIO", 2);
  endfunction

`vmm_class_factory(cpu_scenario)

endclass



