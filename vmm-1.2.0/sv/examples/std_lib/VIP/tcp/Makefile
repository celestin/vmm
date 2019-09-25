#
# Copyright © 2005 Synopsys, Inc.
#
# This VMM library and the associated examples and documentation are confidential
# and proprietary to Synopsys, Inc. Your use or disclosure of this library or
# associated examples or documentation is subject to the terms and conditions
# of a written license agreement between you, or your company, and Synopsys, Inc.
#

VMM	= ../../../src
OPTS	=

include $(VMM)/Makefile.inc

all: test_tcp

test_tcp:
	$(SVTB) $(OPTS)  test_tcp.sv \
                $(SVTBLIBS)
test_err:
	$(SVTB) $(OPTS)  test_err.sv \
                $(SVTBLIBS)
