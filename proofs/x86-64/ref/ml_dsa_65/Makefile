SOURCE = ../../../../formosa-mldsa/x86-64/ref/ml_dsa_65/
COMMON = ../../../../formosa-mldsa/x86-64/ref/common
OARRAYS = ../../../arrays
JASMIN2EC = ../../../../jasmin/compiler/jasmin2ec --output-array=$(OARRAYS)


# --------------------------------------------------------------------
all: ec


ec: 
	env JASMINPATH="Common=$(COMMON)" $(JASMIN2EC) $(SOURCE)/ml_dsa.jazz --array-model=old -o ml_dsa_65.ec \
	  -f ml_dsa_65_keygen \
	  -f ml_dsa_65_sign \
	  -f ml_dsa_65_verify
	env JASMINPATH="Common=$(COMMON)" $(JASMIN2EC) $(SOURCE)/ml_dsa.jazz -o ml_dsa_65_barray.ec \
	  -f ml_dsa_65_keygen \
	  -f ml_dsa_65_sign \
	  -f ml_dsa_65_verify

clean:
	rm -f *.ec
