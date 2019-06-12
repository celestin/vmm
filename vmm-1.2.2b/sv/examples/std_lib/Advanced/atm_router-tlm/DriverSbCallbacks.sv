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
