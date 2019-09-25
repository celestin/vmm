/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/

class Driver extends vmm_xactor;
  virtual router_io.TB router;

  // Input TLM 2.0 blocking socket
  vmm_tlm_b_transport_export#( Driver, Packet, vmm_tlm) socket;
  vmm_tlm_analysis_port#(Driver,Packet) write_port;

  function new(string instance = "class", 
               int stream_id = -1, 
               virtual router_io.TB router);
    super.new("Driver", instance);
    this.stream_id = stream_id;
    this.router    = router;
    `vmm_trace(this.log, $psprintf("%m"));
    socket = new(this, {instance, " in socket"});
    write_port = new(this, {instance, " write_port"});
  endfunction

  virtual task b_transport(int index = -1, vmm_data trans, vmm_tlm phase = null , int delay = -1);
     Packet pkt2send;
     $cast(pkt2send, trans);
     write_port.write(pkt2send);
     send(pkt2send);
  endtask

  virtual task send(Packet pkt2send);
    reg[7:0] datum;
    `vmm_trace(this.log, $psprintf("%m"));
    this.notify.reset(vmm_xactor::XACTOR_IDLE);
    router.cb.frame_n[stream_id] <= 1'b0;
    for(int i=0; i<4; i++) begin
      router.cb.din[stream_id] <= pkt2send.da[i];
      @(router.cb);
    end
    router.cb.din[stream_id] <= 1'b1;
    router.cb.valid_n[stream_id] <= 1'b1;
    repeat(5) @(router.cb);
    while(!router.cb.busy_n[stream_id]) @(router.cb);
    foreach(pkt2send.payload[index]) begin
      datum = pkt2send.payload[index];
      for(int i=0; i<8; i++) begin
        router.cb.din[stream_id] <= datum[i];
        router.cb.valid_n[stream_id] <= 1'b0;
        router.cb.frame_n[stream_id] <= (pkt2send.payload.size() == (index + 1)) && (i==7);
        @(router.cb);
      end
    end
    router.cb.valid_n[stream_id] <= 1'b1;
    this.notify.indicate(vmm_xactor::XACTOR_IDLE);
  endtask

endclass
