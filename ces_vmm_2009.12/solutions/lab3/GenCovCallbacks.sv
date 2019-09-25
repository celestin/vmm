class GenCovCallbacks extends Packet_atomic_gen_callbacks;
   bit[3:0] sa, da;

   covergroup gen_port_cov;
      coverpoint sa;
      coverpoint da;
      cross sa, da;
      type_option.weight = 0;
   endgroup

   function new();
      this.gen_port_cov = new();
   endfunction

   task post_inst_gen(Packet_atomic_gen gen, Packet obj, ref bit drop);
      this.sa = obj.sa;
      this.da = obj.da;
      this.gen_port_cov.sample();
   endtask
endclass
