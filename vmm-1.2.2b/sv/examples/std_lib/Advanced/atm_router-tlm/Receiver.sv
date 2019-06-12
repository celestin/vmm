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

class Receiver extends vmm_xactor;
  virtual router_io.TB router;
  Packet         pktrecvd;

  // Input TLM 2.0 blocking socket
  vmm_tlm_nb_transport_fw_port#(Receiver, Packet) socket = new(this,"Receiver_socket");
  vmm_tlm_analysis_port#(Receiver,Packet) write_port = new(this,"Receiver_analysis_port");
  vmm_tlm::phase_e l_ph;
  int l_delay;

  function new(string instance = "class", int stream_id = -1, virtual router_io.TB router);
    super.new("Receiver", instance);
    `vmm_trace(this.log, $psprintf("%m"));
    this.stream_id = stream_id;
    this.router = router;
    pktrecvd = new();
    pktrecvd.da = this.stream_id;
    pktrecvd.data_id = 0;
    pktrecvd.scenario_id = 0;
  endfunction

  virtual protected task main();
    super.main();
    `vmm_trace(this.log, $psprintf("%m"));
    forever begin
      Packet pkt;
      recv();
      $cast(pkt, pktrecvd.copy());
      write_port.write(pkt);
      socket.nb_transport_fw(pkt,l_ph,l_delay);
    end
  endtask

  task recv();
    Packet   pkt;
    reg[7:0] payload[$];

    `vmm_trace(this.log, $psprintf("%m"));
    this.notify.indicate(vmm_xactor::XACTOR_IDLE);
    fork
      begin @(negedge router.cb.frameo_n[stream_id]); end
      begin
        repeat(100000) @(router.cb);
        `vmm_fatal(this.log, $psprintf("Frame timed out!\n%m\n\n"));
      end
    join_any
    disable fork;
    this.notify.reset(vmm_xactor::XACTOR_IDLE);

    begin
      reg[7:0] datum;
	  int i ;
	  
      payload.delete();

      while(!router.cb.frameo_n[stream_id]) begin
		  i = 0;
		while(i<8) begin	
          if (!router.cb.valido_n[stream_id])
            datum[i++] = router.cb.dout[stream_id];
          if (i == 8) begin
            payload.push_back(datum);
            if (router.cb.frameo_n[stream_id])
              break;
          end
          else if (router.cb.frameo_n[stream_id]) begin
            pktrecvd.display("ERROR");
            `vmm_fatal(this.log, $psprintf("Error with frame signal\n%m\n\n"));
            $finish;
          end
          @(router.cb);
        end
      end
    end

    pktrecvd.payload = new[payload.size()];
    foreach(payload[i])
      pktrecvd.payload[i] = payload[i];

    pktrecvd.data_id++;
  endtask

endclass
