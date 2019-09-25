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

#!/bin/csh -f

simv +vmm_opts+i1=1+b1+s1=x+iy=5+ii=9 +vmm_i2=2 +vmm_b2 +vmm_s2=y +vmm_iz=5 +vmm_ii=5 +vmm_opts_file+./43opts_00basic.opt1+./43opts_00basic.opt2
