// Lab 2a - Include the transaction class and driver class
// ToDo


class cntrlr_env;

   string inst;

   // Lab 2a - Declare an instance of the driver
   // ToDo


   extern function new(string inst);
   extern virtual task reset();
   extern virtual function void build();
   extern virtual task run();

endclass

function cntrlr_env::new(string inst);
   this.inst = inst;
endfunction

task cntrlr_env::reset();
   test_top.reset <= 1'b0;
   repeat(1) @(test_top.cpuif.cb)
   test_top.reset <= 1'b1;
   repeat(10) @(test_top.cpuif.cb)
   test_top.reset <= 1'b0;
endtask

function void cntrlr_env::build();
   // Lab 2a - Construct the driver to drive a total of 5 packets
   // ToDo

endfunction

task cntrlr_env::run();
   // Lab 2a - Call the driver main() to start driver
   // ToDo

endtask
