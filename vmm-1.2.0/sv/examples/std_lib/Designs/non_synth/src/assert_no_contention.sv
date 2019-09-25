/*===========================================================================

Copyright © 2004, 2005 Synopsys, Inc. All rights reserved. 

This SystemVerilog Assertion Example and the associated documentation
are confidential and proprietary to Synopsys, Inc. Your use or
disclosure of this SystemVerilog Assertion Checker is subject to the
terms and conditions of a written license agreement between you, or
your company, and Synopsys, Inc.

===========================================================================*/

/*
 
assert_no_contention

Ensures that bus1 always has a single active driver and that there 
is no X or Z on the bus when driven (en_vector != 0).  
 
The total number of en_vector bits that are asserted can be at most 1.  
bw_en is the number of bits in en_vector. bw_bus is the number
of bits in bus1.
 
min_quiet specifies the minimum number of cycles between bus activity 
during which all bits in en_vector must be 0.  
(Specify 0 for no minimum bus quiet time between bus transactions.)  
 
max_quiet specifies the maximum number of cycles that the bus can
remain quiet (without an active driver). 

Defaults:
 
min_quiet = max_quiet = 0, 
meaning that there is no quiet period between bus transactions.
 
 Failure modes:
 
The assertion assert_no_contention_no_xs will report failure when the
bus had an x or z on one of its bits when at least one driver was
enabled (i.e., when en_vector was not all 0).
 
NOTE: The assertion assert_no_contention_no_xs is eliminated when the
checker is used with Magellan. This is because the tool uses
only 2-state signal values.
 
The assertion assert_no_contention_1_driver will report failure when
there was more than one driver enabled.
 
The assertion assert_no_contention_quiet_time will report failure when
the bus was not quiet for min_quiet clock cycles or that it remained
quiet after max_quiet cycles.  (Or that there was more than one
driver after max_quiet cycles, however, this can be checked by
observing the assertions assert_no_contention_1_driver.)

 
Coverage modes :

cov_level_1_0 (bit 0 set in coverage_level_1) : 

 Cover property, cover_driver_enable, indicates that each bit
 in en_vector was set to 1 (enabled).
  
cov_level_2_0 (bit 0 set in coverage_level_2) :

 Cover point, observed_quiet_cycles, reports the numbers of quiet
 cycles that occurred at least once. 

cov_level_3_0 (bit 0 set in coverage_level_3) :

 Cover property, cover_no_contention_quiet_time_equal_to_min_quiet,
 indicates that the observed quiet time was exactly equal to
 the specified min value.

cov_level_3_1 (bit 1 set in coverage_level_3) :

 Cover property, cover_no_contention_quiet_time_equal_to_max_quiet,
 indicates that the observed quiet time was exactly equal to
 the specified max value.

Example:
 
  assert_no_contention #(0, 0, 0, 2, 32)
        no_contention_inst (clk , 1, bus_enables, bus);
 
verifies that signal "bus" that is 32 bits wide is driven at every
clock cycle because min_quiet = max_quiet = 0, and there are two
drivers because bw_en takes on the default value of 2. reset_n is
a constant 1, hence the checker is enabled all the time. By default,
Level 1 coverage is enabled.
 
*/

`undef SVA_ASSERT_AND_COVER
`ifdef ASSERT_ON
  `define SVA_ASSERT_AND_COVER
`endif
`ifndef SVA_ASSERT_AND_COVER
  `ifdef COVER_ON
     `define SVA_ASSERT_AND_COVER
  `endif
`endif

(* sva_checker *)
interface assert_no_contention( clk, reset_n, en_vector, bus1);  

       parameter              severity_level   = 0;
       parameter              min_quiet        = 0;
       parameter              max_quiet        = 0;
       parameter              bw_en            = 2;
       parameter              bw_bus           = 2; 
       parameter              edge_expr        = 0;
       parameter              msg              = "VIOLATION";
       parameter              category         = 0;
       parameter              coverage_level_1 = 15;
       parameter              coverage_level_2 = 0;
       parameter              coverage_level_3 = 0;
       input                  reset_n;
       input                  clk;
       input  [bw_en-1:0]     en_vector;
       input  [bw_bus-1:0]    bus1;

     `ifdef SVA_ASSERT_AND_COVER
       localparam             assert_name     = "ASSERT_NO_CONTENTION";
       wire                   reset_n;
       wire                   clk;
       wire   [bw_en-1:0]     en_vector;
       wire   [bw_bus-1:0]    bus1;

       wire                   sva_checker_clk;
       reg                    sva_checker_time_0  = 1'b1;

     `include "sva_std_task.h"

       sva_std_edge_select #( severity_level, edge_expr)
         SVA_CHECKER_EDGE_SELECT( clk, sva_checker_clk);

       clocking sampling_ev @(posedge sva_checker_clk);
         input not_resetting, en_vector;
       endclocking : sampling_ev

`ifndef SYNTHESIS
           const int zero = 0;
           logic    [bw_en-1:0]   past_en_vector;
           int                    cnt;

           (* category = category, checkerType = "RANGE", checkerLevel = 2, 
              checkerMin = 0, 
              checkerMax = ( (max_quiet==0) && (min_quiet>0)) ? 
                                      32'hffffffff : max_quiet *)
           covergroup quiet_cycles_cg
                 @( posedge sva_checker_clk);
             coverpoint cnt 
//               iff ( sampling_ev.not_resetting &&
//                     (|sampling_ev.en_vector) && 
               iff ( not_resetting &&
                     (|en_vector) && 
                     ( !(|past_en_vector))  ) {
                 bins observed_quiet_cycle[] = {[1:100]};
                 bins observed_quiet_long = default iff (cnt>0); }

             coverpoint zero 
//               iff (  sampling_ev.not_resetting &&
//                     (|(sampling_ev.en_vector^past_en_vector)) &&
               iff (  not_resetting &&
                     (|(en_vector^past_en_vector)) &&
                     (|past_en_vector)) {
                  bins no_quiet_cycle[] = {0}; }

             option.per_instance = 1;
             option.at_least = 1;
             option.name = "observed_quiet_cycles";
             option.comment = "Bin index is the number of observed quiet cycles";
           endgroup : quiet_cycles_cg

`endif

// Example 7-3 Detecting initial time
       always @ ( posedge sva_checker_clk) begin
         if(not_resetting) 
           sva_checker_time_0 <= 1'b0;
         else
           sva_checker_time_0 <= 1'b1;
       end

     `ifdef COVER_ON
       genvar g;
     `endif

       generate 
`ifndef SYNTHESIS
         if (max_quiet < 0) begin : max_quiet_l_0
              initial sva_checker_error("Illegal max_quiet parameter value < 0");
         end : max_quiet_l_0
`endif

     `ifdef ASSERT_ON

         if (( min_quiet == 0) &&( max_quiet == 0)) begin : min_e_0_max_e_0
             (* category = category *) assert_no_contention_quiet_time :
               assert property( 
                 @( posedge sva_checker_clk)
                   disable iff( !not_resetting) 
                     $countones( en_vector) == 1)
               else sva_checker_error("");
         end : min_e_0_max_e_0

         if (( min_quiet == 0) && ( max_quiet > 0)) begin : min_e_0_max_g_0
             (* category = category *) assert_no_contention_quiet_time :
               assert property( 
                 @( posedge sva_checker_clk)
                   disable iff ( !not_resetting)
                   ( ((en_vector != 0) ##1 (en_vector == 0)) or 
                    sva_checker_time_0 ) 
                       |-> (en_vector == 0)[*1:max_quiet] ##1
                           ($countones(en_vector) == 1) ) 
               else sva_checker_error("");
         end : min_e_0_max_g_0

         if (( min_quiet > 0) && ( max_quiet == 0)) begin : min_g_0_max_e_0
             (* category = category *) assert_no_contention_quiet_time :
               assert property( 
                 @( posedge sva_checker_clk)
                   disable iff ( !not_resetting) 
                    ( ($past(en_vector) != 0) && 
                      ($past(en_vector) != en_vector)) || 
                    (sva_checker_time_0 && (en_vector == 0)) 
                         |-> (en_vector == 0)[*min_quiet])
                 else sva_checker_error("");
         end : min_g_0_max_e_0

         if (( min_quiet > 0) && ( max_quiet >= min_quiet)) begin : min_g_0_max_g_e_min
             (* category = category *) assert_no_contention_quiet_time :
               assert property( 
                 @( posedge sva_checker_clk)
                   disable iff( !not_resetting) 
                     ( ($past(en_vector) != 0) && 
                      ($past(en_vector) != en_vector)) || 
                    (sva_checker_time_0 && (en_vector == 0))
                             |->
                       (en_vector == 0)[*min_quiet:max_quiet] 
                         ##1 ($countones(en_vector) == 1))
                 else sva_checker_error("");
          end : min_g_0_max_g_e_min

`ifndef SYNTHESIS
         if ((max_quiet != 0) && (min_quiet > max_quiet)) begin : max_n_0_min_g_max
             initial sva_checker_error("Illegal max_quiet parameter value < min_quiet");
         end : max_n_0_min_g_max
         if (min_quiet < 0) begin : min_l_0
           initial sva_checker_error("Illegal min_quiet parameter value < 0");
         end : min_l_0
`endif

     `endif // ASSERT_ON
     `ifdef COVER_ON
         if( (coverage_level_1&1 ) != 0) begin : cov_level_1_0
           for( g = 0; g< bw_en; g++) begin : driver
             (* category = category, checkerType = "SEQ", checkerLevel = 1 *) 
               cover_driver_enable:
                 cover property( 
                   @( posedge sva_checker_clk)
                     ( not_resetting && 
                       en_vector[g]));
           end : driver
         end : cov_level_1_0

`ifndef SYNTHESIS
         if( (coverage_level_2&1 ) != 0) begin : cov_level_2_0

           always @ (sampling_ev) begin : count_cycles
             past_en_vector <= sampling_ev.en_vector;
             if( !sampling_ev.not_resetting) begin
               cnt <= 0;
             end
             else 
               if( (!(|sampling_ev.en_vector)) && 
                   ( |past_en_vector || sva_checker_time_0)) begin
                 cnt <= 1;
               end
               else begin
                 cnt <= cnt+1;
               end
           end : count_cycles

           quiet_cycles_cg quiet_cycles_cover = new;

          end : cov_level_2_0
`endif

          if( (coverage_level_3&2 ) != 0) begin : cov_level_3_1
            if( max_quiet > 0 && max_quiet >= min_quiet) begin : max_g_0_max_g_e_min
              (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
                cover_no_contention_quiet_time_equal_to_max_quiet :
                  cover property( 
                    @( posedge sva_checker_clk)
                      ( not_resetting) throughout(
                        ( $past(|en_vector) || sva_checker_time_0) && 
                          ( !(|en_vector)) ##0
                            ( !(|en_vector))[*max_quiet] 
                              ##1 (|en_vector)));
            end : max_g_0_max_g_e_min
          end : cov_level_3_1

          if( (coverage_level_3&1 ) != 0) begin : cov_level_3_0
            if( min_quiet > 0) begin : min_g_0
              (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
                cover_no_contention_quiet_time_equal_to_min_quiet :
                  cover property( 
                    @( posedge sva_checker_clk)
                      ( not_resetting) throughout( 
                        ( $past(|en_vector) || sva_checker_time_0) && 
                          ( !(|en_vector)) ##0
                            ( !(|en_vector))[*min_quiet] 
                              ##1 (|en_vector)));
            end : min_g_0
            if( min_quiet == 0) begin : min_e_0
              (* category = category, checkerType = "LIMIT", checkerLevel = 3 *) 
                cover_no_contention_quiet_time_equal_to_min_quiet :
                  cover property( 
                    @( posedge sva_checker_clk)
                      ( not_resetting) throughout( 
                        ( ( !$stable(en_vector) || sva_checker_tme_0) && 
                          ( $past( |en_vector) || sva_checker_time_0) &&
                          ( |en_vector))));
            end : min_e_0
          end : cov_level_3_0

     `endif // COVER_ON
        endgenerate

     `ifdef ASSERT_ON
      (* category = category *) assert_no_contention_1_driver :
        assert property( 
          @( posedge sva_checker_clk)
            disable iff ( !not_resetting) 
              ($countones( en_vector) <= 1))
        else sva_checker_error("");

// Example 3-44 Non-synthesizable assertion
     `ifdef SVA_CHECKER_FORMAL
     `else
     (* category = category *) assert_no_contention_no_xs :
       assert property( 
         @( posedge sva_checker_clk) 
           disable iff( !not_resetting)
             (^bus1 !== 1'bx) || (en_vector == 0))
         else sva_checker_error("");
     `endif // SVA_CHECKER_FORMAL

     `endif // ASSERT_ON

     `endif // SVA_ASSERT_AND_COVER

endinterface


