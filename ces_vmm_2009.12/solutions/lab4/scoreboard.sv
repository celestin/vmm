`ifndef SCOREBOARD__SV
`define SCOREBOARD__SV

class scoreboard;

   // Lab 3 - Create scoreboard properties
   // ToDo
   test_cfg   cfg;
   vmm_log    log;
   vmm_notify notify;
   int        DONE;
   Packet     coverage_tr;
   Packet     reference_tr[$];
   int        match_cnt;
   int        mismatch_cnt;

   // Lab 3 - Create scoreboard functional coverage
   // ToDo
   covergroup sb_cov;
      coverpoint this.coverage_tr.sa;
      coverpoint this.coverage_tr.da;
      cross this.coverage_tr.sa, this.coverage_tr.da;
   endgroup


   // Lab 3 - Define scoreboard class constructor
   // ToDo
   function new(test_cfg cfg);
      this.cfg = cfg;
      this.log = new("scoreboard", "");
      this.notify = new(this.log);
      this.DONE = this.notify.configure( , vmm_notify::ON_OFF);
      this.match_cnt = 0;
      this.mismatch_cnt = 0;
      this.sb_cov = new();
   endfunction: new


   // Lab 3 - Declare scoreboard class method prototypes:
   // ToDo
   extern virtual function void deposit(vmm_data tr);
   extern virtual function void check(vmm_data tr);
   extern virtual function void report();

endclass


function void scoreboard::report();
   `vmm_note(this.log, $psprintf("%0d transaction matched, %0d mis-matched, %0d orphaned, coverage = %6.2f\n", match_cnt, mismatch_cnt, reference_tr.size, $get_coverage()));
endfunction: report

function void scoreboard::check(vmm_data tr);
   Packet trans;
   int match[$], match_index, found = 0;
   if (!$cast(trans, tr))
      `vmm_fatal(log, "Not a Packet object");
   match = reference_tr.find_index() with (item.da == trans.da);
   foreach (match[i]) begin
      if (reference_tr[match[i]].payload == trans.payload) begin
         match_index = match[i];
         coverage_tr = reference_tr[match[i]];
         sb_cov.sample();
         found = 1;
         break;
      end
   end
   if (found == 0) begin
      `vmm_error(log, trans.psdisplay("[Not Found in Scoreboard]"));
      if ((match_cnt + ++mismatch_cnt) >= this.cfg.run_for_n_packets)
         this.notify.indicate(this.DONE);
      return;
   end
   `vmm_note(log, $psprintf("%0d transaction matched, coverage = %6.2f", ++match_cnt, $get_coverage()));
   `vmm_debug(log, trans.psdisplay());
   reference_tr.delete(match_index);
   if ((match_cnt + mismatch_cnt) >= this.cfg.run_for_n_packets)
      this.notify.indicate(this.DONE);
endfunction: check

function void scoreboard::deposit(vmm_data tr);
   Packet trans;
   if (!$cast(trans, tr))
      `vmm_fatal(log, "Not a Packet object");
   reference_tr.push_back(trans);
endfunction: deposit

`endif
