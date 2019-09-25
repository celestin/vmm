//
// Copyright © 2005 Synopsys, Inc.
//
// This VMM library and the associated examples and documentation are confidential
// and proprietary to Synopsys, Inc. Your use or disclosure of this library or
// associated examples or documentation is subject to the terms and conditions
// of a written license agreement between you, or your company, and Synopsys, Inc.
//

`include "vmm.sv"

interface intel_if;

   wire [31:0] addr;
   wire [31:0] cs;
   wire [31:0] data;
   wire        read;
   wire        write;
   wire        ready;

   modport master (output addr,
                   output cs,
                   inout  data,
                   output read,
                   output write,
                   input  ready);

   modport slave (input  addr,
                  input  cs,
                  inout  data,
                  input  read,
                  input  write,
                  output ready);

   modport passive (input addr,
                    input cs,
                    input data,
                    input read,
                    input write,
                    input ready);
endinterface: intel_if



class intel_transaction extends vmm_data;
   typedef enum {READ, WRITE} kind_e;

   rand kind_e   kind;
   rand bit [31:0] addr;
   rand bit [ 4:0] cs;
   rand bit [31:0] data;
        bit        ok;
endclass: intel_transaction

`vmm_channel(intel_transaction)
`vmm_atomic_gen(intel_transaction, "Intel Cycle")


virtual class intel_master_callbacks extends vmm_xactor_callbacks;

   virtual task pre_tr(intel_master          xactor,
                       ref intel_transaction tr,
                       ref bit               drop);
   endtask

   virtual task post_tr(intel_master        xactor,
                        intel_transaction   tr);
   endtask

endclass: intel_master_callbacks



class intel_master extends vmm_xactor;

   static int unsigned TRANSACTION_STARTED;
   static int unsigned TRANSACTION_COMPLETED;

   virtual intel_if.master   bus;
   intel_transaction_channel in_chan;

   extern function new(string                    inst,
                       virtual intel_if.master   bus,
                       intel_transaction_channel in_chan = null);
   
   extern virtual task read(input  bit [31:0] addr,
                            input  bit [ 4:0] cs,
                            output bit [31:0] data,
                            output bit        ok);

   extern virtual task write(input  bit [31:0] addr,
                             input  bit [ 4:0] cs,
                             input  bit [31:0] data,
                             output bit        ok);

   extern virtual function void reset_xactor(reset_e typ = SOFT_RST);

   extern protected virtual task main();

endclass: intel_master


virtual class intel_slave_callbacks extends vmm_xactor_callbacks;

   virtual function void pre_reply(intel_slave        xactor,
                                   intel_transaction  tr);
   endfunction

   virtual task post_reply(intel_slave        xactor,
                           intel_transaction  tr);
   endtask

   virtual function void post_tr(intel_slave        xactor,
                                 intel_transaction  tr);
   endfunction

endclass: intel_slave_callbacks


class intel_slave extends vmm_xactor;

   static int unsigned TRANSACTION_STARTED;
   static int unsigned TRANSACTION_COMPLETED;

   virtual intel_if.slave    bus;
   intel_transaction_channel req_chan;
   intel_transaction_channel resp_chan;

   extern function new(string                    inst,
                       virtual intel_if.slave    bus,
                       intel_transaction_channel req_chan  = null,
                       intel_transaction_channel resp_chan = null);
   
   extern virtual function void reset_xactor(reset_e typ = SOFT_RST);

   extern protected virtual task main();

endclass: intel_slave


virtual class intel_monitor_callbacks extends vmm_xactor_callbacks;

   virtual function void post_tr(intel_monitor     xactor,
                                 intel_transaction tr);
   endfunction

endclass: intel_monitor_callbacks


class intel_monitor extends vmm_xactor;

   static int unsigned TRANSACTION_STARTED;
   static int unsigned TRANSACTION_COMPLETED;

   virtual intel_if.passive  bus;
   intel_transaction_channel out_chan;

   extern function new(string                    inst,
                       virtual intel_if.passive  bus,
                       intel_transaction_channel out_chan = null);
   
   extern virtual function void reset_xactor(reset_e typ = SOFT_RST);

   extern protected virtual task main();

endclass: intel_monitor

