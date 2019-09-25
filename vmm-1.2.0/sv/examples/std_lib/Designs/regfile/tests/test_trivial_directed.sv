import vmm::*;

program test;

vmm_log log = new("Main", "");

initial
begin
   bit [31:0] rdat;
   bit        ok;

   top.env.gen_cfg();
   top.env.cfg.use_intel_cpu = 1;
   top.env.build();
   top.env.cpu.write(32'h0000_0000, 0, 32'h0000_0000, ok);
   if (!ok) vmm_error(log, "Write did not complete succesfully");

   top.env.cpu.read(32'h0000_0000, 0, rdat, ok);
   if (!ok) vmm_error(log, "Read did not complete succesfully");
   if (rdat !== '0) vmm_error(log, "Invalid readback value");
   log.report();
end

endprogram: test
