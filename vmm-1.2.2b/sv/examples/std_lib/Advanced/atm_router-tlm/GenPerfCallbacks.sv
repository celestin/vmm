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

class GenPerfCallbacks extends Packet_atomic_gen_callbacks;

  Environment  my_env;
  int start_time, end_time;
  int tenure_id, initiator_id, target_id,trans;

  function new(Environment env);
    this.my_env = env;
  endfunction

  virtual task post_inst_gen(Packet_atomic_gen gen, Packet obj, ref bit drop);
    fork
     begin
      vmm_perf_tenure tenure = new(gen.stream_id,,obj);
      obj.notify.wait_for(vmm_data::STARTED);
      this.my_env.tr_perf.start_tenure(tenure);
      obj.notify.wait_for(vmm_data::ENDED);
      this.my_env.tr_perf.end_tenure(tenure);
     end
    join_none
  endtask

endclass
