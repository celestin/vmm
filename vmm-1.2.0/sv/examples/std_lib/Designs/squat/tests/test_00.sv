program test;

initial
begin
   top.env.gen_cfg();
   top.env.cfg.run_for = 1;
   top.env.start();
   top.env.gen[1].stop_xactor();
   top.env.gen[2].stop_xactor();
   top.env.gen[3].stop_xactor();
   top.env.run();
end
endprogram
