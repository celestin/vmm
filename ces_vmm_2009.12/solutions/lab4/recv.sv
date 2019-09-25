`ifndef RECV_SV
`define RECV_SV

task Receiver::recv(Packet tr);
   static int obj_cnt[16];
   reg[7:0] datum;
   `vmm_trace(this.log, $psprintf("%m"));

   fork
      @(negedge sigs.sclk.frameo_n[stream_id]);
      begin
         repeat(10000) @(sigs.sclk);
         `vmm_fatal(log, "Frame timed out");
      end
   join_any
   disable fork;

   tr.stream_id = this.stream_id;
   tr.da = this.stream_id;
   tr.notify.indicate(vmm_data::STARTED);
   this.notify.indicate(this.OBSERVING, tr);

   `vmm_trace(this.log, "Starting transaction...");

   while(!sigs.sclk.frameo_n[stream_id]) begin
      for(int i=0; i<8; i=i) begin
         if (!sigs.sclk.valido_n[stream_id]) begin
            datum[i++] = sigs.sclk.dout[stream_id];
         end
         if (i == 8) begin
            tr.payload.push_back(datum);
            if (sigs.sclk.frameo_n[stream_id]) begin
               tr.status = Packet #()::IS_OK;
               break;
            end
         end
         else if (sigs.sclk.frameo_n[stream_id]) begin
            tr.status = Packet #()::ERROR;
            `vmm_fatal(this.log, $psprintf("%s\nError with frame signal\n%m\n\n", tr.psdisplay()));
            break;
         end
         @(sigs.sclk);
      end
   end

   tr.data_id = obj_cnt[stream_id]++;

   `vmm_trace(this.log, "Completed transaction...");
   `vmm_debug(this.log, tr.psdisplay("   "));

   this.notify.reset(this.OBSERVING);
   tr.notify.indicate(vmm_data::ENDED);
endtask: recv

`endif
