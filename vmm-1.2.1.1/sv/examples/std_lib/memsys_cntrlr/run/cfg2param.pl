#!/usr/local/bin/perl -w

##
## -------------------------------------------------------------
##    Copyright 2004-2009 Synopsys, Inc.
##    All Rights Reserved Worldwide
##
##    Licensed under the Apache License, Version 2.0 (the
##    "License"); you may not use this file except in
##    compliance with the License.  You may obtain a copy of
##    the License at
##
##        http://www.apache.org/licenses/LICENSE-2.0
##
##    Unless required by applicable law or agreed to in
##    writing, software distributed under the License is
##    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
##    CONDITIONS OF ANY KIND, either express or implied.  See
##    the License for the specific language governing
##    permissions and limitations under the License.
## -------------------------------------------------------------
##

# This script converts RTL config to parameters of the controller block
# This is for demonstration just for this case. Users can have their own way 

$rtl_cfg_file = $ARGV[0];
open (RFILE, $rtl_cfg_file) || die "Cant Open RTL config file $!";
open (PFILE, ">param.txt") || die "Cant open param.txt for writing";
while (<RFILE>) {
  if ($_ =~ /num_sram_devices\s*:\s*(\d+);/) {
     print PFILE "assign $1 test_top/NUM_OF_SRAMS\n";
  } elsif ($_ =~ /sram_size_str\s*:\s*SIZE_(\d+);/) {
     $sze = 1;
     $wdth = 1;
     while ($sze != $1) {
       $wdth++;
       $sze = 2 ** $wdth;
     }
     print PFILE "assign $wdth test_top/RAM_ADDR_WDTH\n";
  }
}
close RFILE;
