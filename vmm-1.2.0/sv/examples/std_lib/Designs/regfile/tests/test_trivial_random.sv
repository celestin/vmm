import vmm::*;

program test;

vmm_log log = new("Main", "");

class trivial intel_transaction extends intel_transaction;
   constraint trivial {
      addr == 32'h0000_0000;
      cs   == 0;
      if (object_id == 0) kind == WRITE;
      if (object_id == 1) kind == READ;
   }
endclass: trivial_intel_transaction

initial
begin
   bit [31:0] rdat;
   bit        ok;

   top.env.gen_cfg();
   top.env.cfg.run_for = 2;

   top.env.build();
   begin
      trivial_intel_transaction tr = new;
      top.env.gen.randomized_obj = tr;
   end

   top.env.run();
end

endprogram: test
