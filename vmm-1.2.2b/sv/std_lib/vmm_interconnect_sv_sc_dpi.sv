/*********************************************************************
 * SYNOPSYS CONFIDENTIAL                                             *
 *                                                                   *
 * This is an unpublished, proprietary work of Synopsys, Inc., and   *
 * is fully protected under copyright and trade secret laws. You may *
 * not view, use, disclose, copy, or distribute this file or any     *
 * information contained herein except pursuant to a valid written   *
 * license from Synopsys.                                            *
 *********************************************************************/
`ifndef VMM_INTERCONNECT_SV_SC_DPI
`define VMM_INTERCONNECT_SV_SC_DPI

// events used in SV-SC flow
event  req_ev_to_sc;
event  rcvd_ev_from_sc;

//events used in SC-SV flow
event  req_ev_to_sv;
event  rcvd_ev_from_sv;

// SV imported tasks
import "DPI" function void vmm_sc_dpi_notify(chandle ready);
import "DPI" function void vmm_sc_register_dpi_scope();

// SV exported tasks (SV-SC)
export "DPI" task vmm_sc_run_ph;
export "DPI" task vmm_sc_get_ph_name;
export "DPI" task vmm_sc_ph_done;

// SV exported tasks (SC-SV)
export "DPI" task vmm_sv_run_ph;

// SV exported tasks used in vmm_opts interop flow
export "DPI" task vmm_sc_get_opts_bit;
export "DPI" task vmm_sc_get_opts_int;
export "DPI" task vmm_sc_get_opts_str;
export "DPI" task vmm_sc_get_opts_obj;
export "DPI" task vmm_sc_get_opts_range;

// queue to store phase name (SV-SC)
string req_ph_sc_q[$];
// queue to store phase name (SC-SV)
string req_ph_sv_q[$];

function register_dpi_scope();
   //string scope = "$unit";
   vmm_sc_register_dpi_scope();
endfunction


/**********************************************************
*               Functions to be invoked on SV-SC side
***********************************************************/
/// task to be invoked on SV side (SV-SC flow).
task automatic vmm_sv2sc_sync_phase( input string phase);
   ->req_ev_to_sc;
   req_ph_sc_q.push_back(phase); 
   @rcvd_ev_from_sc;
endtask
   
//  ****************   Exported Tasks *********
// SV Exported Tasks (SV-SC flow)
// *******************************************

task automatic  vmm_sc_run_ph(input chandle ready);
   fork
      vmm_sc_run_ph_1(ready);
   join_none   
endtask

task automatic  vmm_sc_run_ph_1(input chandle ready);
   if(req_ph_sc_q.size() == 0)      
      @req_ev_to_sc;
   vmm_sc_dpi_notify(ready);
endtask

// SV Exported Tasks (SV-SC flow)
task automatic vmm_sc_get_ph_name(output string ph_name);
   ph_name = req_ph_sc_q.pop_front();
endtask

// SV Exported Tasks (SV-SC flow)
task automatic  vmm_sc_ph_done();
   ->rcvd_ev_from_sc;
endtask

// **********************************************************
//  task to be invoked on SV side (SC-SV flow)
// ********************************************
task automatic vmm_sc2sv_sync_phase(output string phase);
   if(req_ph_sv_q.size() == 0)
      @req_ev_to_sv;
   phase = req_ph_sv_q.pop_front();
endtask

task automatic vmm_sc2sv_sync_phase_over();
   ->rcvd_ev_from_sv;
endtask

//  ****************   Exported Tasks *********
// SV Exported Tasks  for SC (SC-SV flow)
// ********************************************
task automatic vmm_sv_run_ph(input string ph_name,chandle ready);
   fork
      vmm_sv_run_ph_1(ph_name,ready);
   join_none
endtask

task automatic vmm_sv_run_ph_1(input string ph_name,chandle ready);
   ->req_ev_to_sv;
   req_ph_sv_q.push_back(ph_name);
   @rcvd_ev_from_sv;
   vmm_sc_dpi_notify(ready);
endtask


/// Taks used in vmm_opts interop flow
task automatic vmm_sc_get_opts_bit(input string hier, string name, output bit val, output bit opt_specified);

   vmm_opts_info oinfo;
   oinfo = vmm_opts::send_opts(name,vmm_opts_info::BOOL_ARGS,0,"",hier);
   val = oinfo.val; 
   opt_specified = oinfo.opt_specified;
endtask

task automatic vmm_sc_get_opts_int(input string hier, string name, output int val,output bit opt_specified);
   vmm_opts_info oinfo;
   oinfo = vmm_opts::send_opts(name,vmm_opts_info::INT_ARGS,0,"",hier);
   val = oinfo.val;
   opt_specified = oinfo.opt_specified;
endtask

task automatic vmm_sc_get_opts_str(input string hier, string name, output string str, output bit opt_specified);
   vmm_opts_info oinfo;
   oinfo = vmm_opts::send_opts(name,vmm_opts_info::STR_ARGS,0,"",hier);
   str = oinfo.sarg;
   opt_specified = oinfo.opt_specified;

endtask

task automatic vmm_sc_get_opts_obj(input string hier, string name, output chandle obj);
/*
   vmm_opts_info oinfo;
   oinfo = vmm_opts::send_opts(name,vmm_opts_info::OBJ_ARGS,0,"",hier);
   obj = oinfo.obj;
*/
endtask

task automatic vmm_sc_get_opts_range(input string hier, string name, output int min, output int max, output bit opt_specified);

   vmm_opts_info oinfo;
   oinfo = vmm_opts::send_opts(name,vmm_opts_info::RANGE_ARGS,0,"",hier);
   min = oinfo.min;  
   max = oinfo.max;
   opt_specified = oinfo.opt_specified;
endtask
`endif
