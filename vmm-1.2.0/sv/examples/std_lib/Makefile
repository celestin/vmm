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
	(cd factory_pattern/basic_param_class; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_user_defined_class; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_vmm_data; gmake -k Makefile $(TAG))
	(cd factory_pattern/basic_vmm_object; gmake -k Makefile $(TAG))
	(cd factory_pattern/multi_gen_array; gmake -k Makefile $(TAG))
	(cd factory_pattern/multi_intance_gen; gmake -k Makefile $(TAG))
	(cd factory_pattern/multiple_factory_classes_by_copy; gmake -k Makefile $(TAG))
	(cd factory_pattern/factory_set_cfg; gmake -k Makefile $(TAG))
	(cd hierarchical_options/display_options_with_get_help; gmake -k Makefile $(TAG))
	(cd hierarchical_options/global_get_option_command_line; gmake -k Makefile $(TAG))
	(cd hierarchical_options/global_get_option_file; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_bit_objs_across_hier; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_int_val_specific_hier; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_val_integer_range; gmake -k Makefile $(TAG))
	(cd hierarchical_options/option_val_specific_obj; gmake -k Makefile $(TAG))
	(cd hierarchical_options/set_object_type_options; gmake -k Makefile $(TAG))
	(cd phasing/concurrent_time_line; gmake -k Makefile $(TAG))
	(cd phasing/hierarchical_time_line; gmake -k Makefile $(TAG))
	(cd phasing/phase_methods; gmake -k Makefile $(TAG))
	(cd phasing/phase_vmm_test; gmake -k Makefile $(TAG))
	(cd phasing/phase_vmm_unit; gmake -k Makefile $(TAG))
	(cd rtl_config; gmake -k Makefile $(TAG))
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
	(cd Advanced/wimaxgen; gmake -k Makefile $(TAG))
	(cd Advanced/uproc; gmake -k Makefile $(TAG))
	(cd Advanced/memsys; gmake -k Makefile $(TAG))
	(cd Advanced/atm_router-tlm; gmake -k Makefile $(TAG))

