class memsys_trans extends cpu_trans;
  rand int cpuid;

  constraint cst_id {
    cpuid inside {[0:1]};
  }

   `vmm_data_member_begin(memsys_trans)
   `vmm_data_member_scalar(cpuid, DO_ALL)
   `vmm_data_member_end(memsys_trans)

  `vmm_class_factory(memsys_trans)

endclass
`vmm_channel(memsys_trans)
`vmm_scenario_gen(memsys_trans, "MEMSYS scenario generator")

