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

ifdef VMM_HOME
OPTS = +define+VMM_12 +incdir+$(VMM_HOME)/sv
else
OPTS = +define+VMM_12 -ntb_opts rvm
endif

ifndef TAG
TAG = all
endif

all: sim

sim:
	(cd Advanced/atm_router-tlm; gmake -k Makefile $(TAG))
	(cd Advanced/memsys-tblog; gmake -k Makefile $(TAG))
	(cd Advanced/memsys; gmake -k Makefile $(TAG))
	(cd Advanced/uproc; gmake -k Makefile $(TAG))
	(cd Advanced/wimaxgen; gmake -k Makefile $(TAG))
	(cd VIP/Exec_Models/in_order; gmake -k Makefile $(TAG))
	(cd VIP/Exec_Models/non_atomic; gmake -k Makefile $(TAG))
	(cd VIP/Exec_Models/out_of_order; gmake -k Makefile $(TAG))
	(cd VIP/Exec_Models/passive; gmake -k Makefile $(TAG))
	(cd VIP/Exec_Models/reactive; gmake -k Makefile $(TAG))
	(cd VIP/Legacy; gmake -k Makefile $(TAG))
	(cd VIP/ethernet; gmake -k Makefile $(TAG))
	(cd VIP/tcp; gmake -k Makefile $(TAG))
	(cd VIP/wishbone; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_param_class; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_user_defined_class; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_vmm_data; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_vmm_object; gmake -k Makefile $(TAG))
	(cd factory_pattern/factory_set_cfg; gmake -k Makefile $(TAG))
	(cd factory_pattern/multi_gen_array; gmake -k Makefile $(TAG))
	(cd factory_pattern/multi_intance_gen; gmake -k Makefile $(TAG))
	(cd factory_pattern/multiple_factory_classes_by_copy; gmake -k Makefile $(TAG))
	(cd hierarchical_options/display_options_with_get_help; gmake -k Makefile $(TAG))
	(cd hierarchical_options/global_get_option_command_line; gmake -k Makefile $(TAG))
	(cd hierarchical_options/global_get_option_file; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_bit_objs_across_hier; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_int_val_specific_hier; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_val_integer_range; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_val_specific_obj; gmake -k Makefile $(TAG))
	(cd hierarchical_options/set_object_type_options; gmake -k Makefile $(TAG))
	(cd log_catcher; gmake -k Makefile $(TAG))
	(cd memsys_cntrlr/run; gmake -k Makefile $(TAG))
	(cd mss_simple; gmake -k Makefile $(TAG))
	(cd name_space/vmm_object_namespace; gmake -k Makefile $(TAG))
	(cd opts; gmake -k Makefile $(TAG))
	(cd phasing/concurrent_time_line; gmake -k Makefile $(TAG))
	(cd phasing/hierarchical_time_line; gmake -k Makefile $(TAG))
	(cd phasing/phase_methods; gmake -k Makefile $(TAG))
	(cd phasing/phase_vmm_group; gmake -k Makefile $(TAG))
	(cd phasing/phase_vmm_test; gmake -k Makefile $(TAG))
	(cd record_replay; gmake -k Makefile $(TAG))
	(cd rtl_config; gmake -k Makefile $(TAG))
	(cd scenarios; gmake -k Makefile $(TAG))
	(cd simulation/vmm_simulation_methods; gmake -k Makefile $(TAG))
	(cd simulation/vmm_test_macro; gmake -k Makefile $(TAG))
	(cd tlm/tlm_analysis; gmake -k Makefile $(TAG))
	(cd tlm/tlm_analysis_macro; gmake -k Makefile $(TAG))
	(cd tlm/tlm_basic_example; gmake -k Makefile $(TAG))
	(cd tlm/tlm_bidirectional_transport; gmake -k Makefile $(TAG))
	(cd tlm/tlm_import_nb_transport; gmake -k Makefile $(TAG))
	(cd tlm/tlm_import_sockets; gmake -k Makefile $(TAG))
	(cd tlm/tlm_interconnect; gmake -k Makefile $(TAG))
	(cd tlm/tlm_nb_transport; gmake -k Makefile $(TAG))
	(cd tlm/tlm_nb_transport_macro; gmake -k Makefile $(TAG))
	(cd tlm/tlm_sockets; gmake -k Makefile $(TAG))
	(cd vmm_test/run; gmake -k Makefile $(TAG))
	(cd Designs/oc_fpu/test_bench_vmm/tests; gmake -k Makefile $(TAG))
