//
// -------------------------------------------------------------
//    Copyright 2004-2009 Synopsys, Inc.
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

class Driver extends vmm_xactor;
  virtual router_io.TB router;

  // Input TLM 2.0 blocking socket
  vmm_tlm_b_transport_export#( Driver, Packet) socket;
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

  virtual task b_transport(int index = -1, vmm_data trans, ref int delay);
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
