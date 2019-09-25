`ifndef SEND_SV
`define SEND_SV

task Driver::send_address(Packet tr);
   `vmm_trace(this.log, $psprintf("%m"));
   sigs.mclk.frame_n[stream_id] <= 1'b0;
   for(int i=0; i<4; i++) begin
      sigs.mclk.din[stream_id] <= tr.da[i];
      @(sigs.mclk);
   end
endtask: send_address

task Driver::send_pad(Packet tr);
   `vmm_trace(this.log, $psprintf("%m"));
   sigs.mclk.din[stream_id] <= 1'b1;
   sigs.mclk.valid_n[stream_id] <= 1'b1;
   repeat(5) @(sigs.mclk);
endtask: send_pad

task Driver::send_payload(Packet tr);
   reg[7:0] datum;
   `vmm_trace(this.log, $psprintf("%m"));
   while(!sigs.mclk.busy_n[stream_id]) @(sigs.mclk);
   foreach(tr.payload[index]) begin
      datum = tr.payload[index];
      for(int i=0; i<8; i++) begin
        sigs.mclk.din[stream_id] <= datum[i];
        sigs.mclk.valid_n[stream_id] <= 1'b0;
        sigs.mclk.frame_n[stream_id] <= (tr.payload.size() == (index + 1)) && (i==7);
        @(sigs.mclk);
      end
   end
   sigs.mclk.valid_n[stream_id] <= 1'b1;
endtask: send_payload

`endif
