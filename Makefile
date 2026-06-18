# -*- Makefile -*-

# --------------------------------------------------------------------
EASYCRYPT ?= easycrypt
ECFLAGS   ?=
ECJOBS    ?= 3
ECRUNTEST ?= $(EASYCRYPT) runtest -jobs $(ECJOBS) $(ECFLAGS)

# --------------------------------------------------------------------
PHONY: default check clean

# --------------------------------------------------------------------
default: check

# --------------------------------------------------------------------
check:
	$(ECRUNTEST) config/tests.config all

# --------------------------------------------------------------------
clean:
	find proofs -name '*.eco' -print0 | xargs -0 rm -f
