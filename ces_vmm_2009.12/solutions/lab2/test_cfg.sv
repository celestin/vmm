`ifndef TEST_CFG__SV
`define TEST_CFG__SV

class test_cfg;
   // Lab 1 - Create random configuraton properties
   //         - run_for_n_packets: to control number of packets per test
   //         - num_of_iports: number of input ports to test
   //         - num_of_oports: number of output ports to test
   //         - iports_in_use[]: array of ON/OFF flags for input ports
   //         - oports_in_use[]: array of ON/OFF flags for output ports
   // ToDo
   rand int run_for_n_packets; // number of packets to process for test
   rand int num_of_iports;     // number of input ports to be tested
   rand int num_of_oports;     // number of output ports to be tested
   rand bit iports_in_use[];   // array of ON/OFF flags for input ports
   rand bit oports_in_use[];   // array of ON/OFF flags for output ports


   constraint testcase;  // Leave blank.  To be defined in testcase

   constraint valid {
     // Lab 1 - Define valid spec constraints
     // ToDo
     run_for_n_packets inside {[1:10000]};
     num_of_iports inside {[1:16]};
     num_of_oports inside {[1:16]};
     iports_in_use.sum() == num_of_iports;
     oports_in_use.sum() == num_of_oports;
   }
    
   function new();
     // Lab 1 - Allocate size of ON/OFF flag dynamic array to spec size
     // ToDo
     iports_in_use = new[16];
     oports_in_use = new[16];
   endfunction

   extern virtual function string psdisplay(string prefix = "");
endclass: test_cfg

// Lab 1 - Add an include statement for the psdisplay method definition
// ToDo
`include "psdisplay.sv"


`endif // TEST_CFG__SV
