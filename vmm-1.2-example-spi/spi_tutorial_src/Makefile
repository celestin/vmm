##############################################################################
#
#  DDDDD   OOO  UU UU LL    OOO   SSS
#  DD  DD OO OO UU UU LL   OO OO SS  S
#  DD  DD OO OO UU UU LL   OO OO  SS
#  DD  DD OO OO UU UU LL   OO OO   SS
#  DD  DD OO OO UU UU LL   OO OO S  SS
#  DDDDD   OOO   UUU  LLLL  OOO   SSS
#
#  Doulos
#
#  Filename: Makefile
#  Date: 2 Nov 2009
#  Author: Doug Smith
#  Description:  Makefile to build the VMM WB-SPI environment.
#
##############################################################################

##############################################################################
# Edit the following variables:
#
#   RTL_DIR - download the SPI model from OpenCores at
#             http://www.opencores.org/project,spi,overview
#             and set RTL_DIR to the rtl directory
#
#   VMM_DIR - download VMM 1.2 from www.vmmcentral.org and specify path to
#             the sv directory
#
#   VCS_OPTS - change these options if you like, but these should work OK
#
##############################################################################

RTL_DIR		= ../../rtl
VMM_DIR		= ../../../../vmm/vmm1.2/vmm-1.2/sv
VCS_OPTS	= -sverilog -y $(VMM_DIR) +libext+.v +libext+.svh +libext+.sv +incdir+$(VMM_DIR) +incdir+$(RTL_DIR)


##############################################################################
# You should not need to edit pass this line unless you want to enable the
# +vmm_test option
##############################################################################

# VCS hack for Fedora linux
export VCS_ARCH_OVERRIDE = linux

#-------------------------------
#- Tool paths and options
#-------------------------------
VMM_FILES 	= $(VMM_DIR)/vmm.sv
VCS		= vcs

#-------------------------------
#- Source files
#-------------------------------
RTL_FILES	= $(RTL_DIR)/timescale.v \
		  $(RTL_DIR)/spi_clgen.v \
		  $(RTL_DIR)/spi_defines.v \
		  $(RTL_DIR)/spi_shift.v \
		  $(RTL_DIR)/spi_top.v

WRAPPER 	= spi_wrapper.sv

INTERFACE_FILES	= dut_intf.sv

TB_FILES	= wb_spi_pkg.sv \
		  wb_spi_tb.sv \
		  wb_spi_top.sv

TEST		= wb_test1

ALL_FILES 	= $(RTL_FILES) \
		  $(INTERFACE_FILES) \
		  $(WRAPPER) \
		  $(TB_FILES)

#-------------------------------
#- Targets
#-------------------------------
build:	$(ALL_FILES)
	$(VCS) $(VCS_OPTS) $?

sim:	$(ALL_FILES)
	$(VCS) -R $(VCS_OPTS) $? -l output #+vmm_test=$(TEST)

debug:	$(ALL_FILES)
	$(VCS) -R $(VCS_OPTS) -gui -debug_all $? -l output #+vmm_test=$(TEST)
