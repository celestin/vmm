import vmm::*;
import atm::*;

program squat_self_check;

class sb_cells;
   atm_cell cells[$];
endclass

class scoreboard;

   vmm_log log = new("Scoreboard", "");

   test_cfg cfg;

   sb_cells  expect[0:3][0:3];  // from port [i] -> port [j]
   bit [3:0] will_be_bad;

   function new();
      foreach (expect[i,j]) begin
         expect[i,j] = new;
      end
      will_be_bad = 4'h0;
   endfunction

endclass: scoreboard

const scoreboard sb = new;



function void configure(test_cfg new_cfg);
   sb.cfg = new_cfg;
endfunction

function void injected_cell(atm_cell cell,
                            int      on_port);
   atm_uni_cell uni;
   atm_nni_cell nni;
   bit [7:0] bytes[];

   if (!$cast(uni, cell)) begin
      `vmm_error(log, "A non-UNI cell was injected");
      return;
   end

   // Is this a bad cell?
   if (cell.hec !== 8'h00) begin
      return; // Will be dropped
   end

   // Has this cell been corrupted via error injection?
   if (sb.will_be_bad[on_port]) begin
      sb.will_be_bad[on_port] = 0;
      return; // Will be dropped
   end

   // Rewrite the cell
   void'(uni.byte_pack(bytes));
   nni = new;
   void'(nni.byte_unpack(bytes));
   nni.vpi = sb.cfg.dut.uni_vpi[uni.vpi].nni_vpi;

   // Add to the expected list of cell to the forwarded ports
   for (int i = 0; i < 4; i++) begin
      atm_nni_cell cell;

      if (!cfg.dut.uni_vpi[uni.vpi].forward[i]) continue;

      $cast(cell, nni.copy());
      sb.expect[on_port][i].cells.push_back(cell);
   end
endfunction

function void received_cell(atm_cell cell,
                            int      on_port);

   // Must be the next cell expected on this output port
   // from one of the input ports
   foreach (sb.expect[i]) begin
      atm_nni_cell exp = sb.expect[i, on_port].cells.front();
      if (exp == null || !cell.compare(exp)) continue;

      // Expected!
      void'(sb.expect[i, on_port].cells.pop_front());
      return;
   end
   `vmm_error(log, $psprintf("Unexpected cell received on por #%0d:\n%s,
                             on_port, cell.psdisplay("   ")));
endfunction

endprogram
