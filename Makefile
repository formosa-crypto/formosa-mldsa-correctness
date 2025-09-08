# -*- Makefile -*-

# --------------------------------------------------------------------
EASYCRYPT ?= easycrypt
ECFLAGS   ?= 
ECRUNTEST ?= $(EASYCRYPT) runtest $(ECFLAGS)

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
