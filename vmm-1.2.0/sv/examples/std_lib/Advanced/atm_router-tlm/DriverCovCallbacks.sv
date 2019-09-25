/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class DriverCovCallbacks extends vmm_object;
  bit[3:0] sa, da;

  vmm_tlm_analysis_export#(DriverCovCallbacks,Packet) write_port = new(this, "DriverCovCallbacks", 100, 0);

  covergroup drvr_port_cov;
    coverpoint sa;
    coverpoint da;
    cross sa, da;
    option.weight = 0;
  endgroup

  function new(string name = "", vmm_object parent=null);
    super.new(parent, name);
    drvr_port_cov = new();
  endfunction

  virtual function write(int id = -1, Packet obj);
    this.sa = obj.sa;
    this.da = obj.da;
    drvr_port_cov.sample();
  endfunction : write

endclass
