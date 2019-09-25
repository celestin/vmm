#!/bin/sh

if [ "$1" = clean ] ; then
  rm -rf *.log *.log.filtered *.wlf transcript* work questa.do; exit
fi

if [ -z "$1" ] ; then
LIST="test_trivial_rx test_trivial_tx test_unconstrained test_directed test_sequences test_rx_err"
else
LIST=$1
fi

if [ -z "$VMM_HOME" ] ; then
${VMM_HOME:=../../../../..}
fi

if [ -z "$VMM_DPI_DIR" ] ; then
${VMM_DPI_DIR:=$VMM_HOME/shared/lib/linux_x86_64}
fi


# internal use only
EX=$VMM_HOME/sv/examples
check () {
  if [ -n "$INTEROP_REGRESS" ] ; then
    perl $EX/regress/regress_passfail.pl $EXAMPLE.log "std_lib/oc_ethernet/tests" $EX/results.log
  fi
}

#------------------------------------------------------------------------

echo "set SolveArrayResizeMax 5000; run -all; quit" > questa.do

VLOG_ARGS="-mfcu -sv +incdir+$VMM_HOME/sv+.
           -L $VMM_HOME/shared/examples/oc_ethernet/rtl/work_rtl
           +incdir+$VMM_HOME/sv/examples/std_lib/wishbone \
           +incdir+$VMM_HOME/sv/examples/std_lib/ethernet 
           -suppress 2227 +define+OC_ETHERNET_BUG"

VSIM_ARGS="-c -do questa.do -sv_lib $VMM_DPI_DIR/vmm_str_dpi
           -L $VMM_HOME/shared/examples/oc_ethernet/rtl/work_rtl
           tb_top tb_top_env "

pushd $VMM_HOME/shared/examples/oc_ethernet/rtl
vlib work_rtl
vlog -work work_rtl -f rtl_file_list.lst +define+SINGLE_RAM_VARIABLE
popd


vlib work

for EXAMPLE in $LIST; do

  vlog $VLOG_ARGS $EXAMPLE.sv ../tb_top.sv && \
  vsim $VSIM_ARGS $EXAMPLE mii_mac_bfm -l $EXAMPLE.log

  check

done

