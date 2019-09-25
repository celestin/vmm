//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "tcp.sv"

class test_cfg;
   rand tcp_sessions_cfg sessions;

   function new();
      this.sessions = new;
   endfunction: new

   function string psdisplay(string prefix = "");
      psdisplay = this.sessions.psdisplay({prefix, "Sessions: "});
   endfunction
endclass: test_cfg

class tcp_env extends vmm_env;

   test_cfg cfg;

   tcp_sessions sessions;
   tcp_server   server;

   function new();
      $timeformat(-9, 0, "ns", 1);
      this.cfg = new;
   endfunction: new


   virtual function void gen_cfg();
      bit ok;
      super.gen_cfg();

      ok = this.cfg.randomize();
      if (!ok) `vmm_fatal(this.log, "Unable to randomize test configuration...");
   endfunction: gen_cfg


   virtual function void build();
      super.build();

      $write("Test cfg:\n%s\n", this.cfg.psdisplay("   "));

      this.sessions = new("", 0, cfg.sessions);
      this.server   = new("", 0, this.sessions.out_chan, this.sessions.in_chan);
   endfunction: build
     

   virtual task start();
      super.start();

      this.sessions.start_xactor();
      this.server.start_xactor();
   endtask: start

   virtual task wait_for_end();
      super.wait_for_end();

      this.sessions.notify.wait_for(this.sessions.DONE);
   endtask: wait_for_end


   virtual task check_response();
   endtask
     
endclass
