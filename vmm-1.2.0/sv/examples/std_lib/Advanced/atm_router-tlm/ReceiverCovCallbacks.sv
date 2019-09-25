/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class ReceiverCovCallbacks extends vmm_object;
  vmm_tlm_analysis_export#(ReceiverCovCallbacks,Packet) write_port = new(this, "ReceiverCovCallbacks", 100, 0 );
  bit[3:0] da;

  covergroup rcvr_port_cov;
    coverpoint da;
    option.weight = 0;
  endgroup

  function new(string name = "", vmm_object parent);
    super.new(parent, name);
    rcvr_port_cov = new();
  endfunction

  virtual function write(int id = -1, Packet obj);
    this.da = obj.da;
    rcvr_port_cov.sample();
  endfunction : write

endclass
