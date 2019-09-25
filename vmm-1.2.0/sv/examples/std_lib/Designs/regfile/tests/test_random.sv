import vmm::*;

program test;

vmm_log log = new("Main", "");

initial
begin
   top.env.run();
end

endprogram: test
