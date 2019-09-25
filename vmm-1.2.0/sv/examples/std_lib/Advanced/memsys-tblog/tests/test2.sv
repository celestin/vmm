class test2 extends vmm_test;
  `vmm_typename(test2)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void build_ph();
     vmm_opts::set_int("num_scenarios", 15, this);
  endfunction

endclass
test2 tst2 = new("test2");
