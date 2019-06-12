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
