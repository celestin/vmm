class test1 extends vmm_test;
  `vmm_typename(test1)

  function new(string name);
     super.new(name);
  endfunction

  virtual function void build_ph();
     vmm_opts::set_int("num_scenarios", 10, this);
  endfunction

endclass
test1 tst1 = new("test1");
