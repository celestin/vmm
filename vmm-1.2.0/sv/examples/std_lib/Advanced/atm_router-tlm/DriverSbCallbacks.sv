/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class DriverSbCallbacks extends vmm_object;
  vmm_tlm_analysis_export#(DriverSbCallbacks,Packet) write_port = new(this, "DriverSbCallbacks", 100, 0);

  Scoreboard sb;
  function new(Scoreboard sb, string name="", vmm_object parent);
    super.new(parent, name);
    this.sb = sb;
  endfunction

  virtual function write(int id = -1, Packet obj);
    this.sb.deposit_sentpkt(obj);
  endfunction : write

endclass
