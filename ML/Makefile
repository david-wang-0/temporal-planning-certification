.PHONY: tp_to_muntax

MLUNTA_DIR="../../mlunta"
MLUNTAC:="./$(MLUNTA_DIR)/build/mluntac-mlton"

MUNTA_DIR="../../munta/ML"
MUNTAC:="./$(MUNTA_DIR)/muntac_mlton"

DOMAIN?="none"
PROBLEM?="none"
OUTPUT?="none"
CERTIFICATE?="none"
RENAMING?="none"

build_tp_conversion: 
	mlton -default-type int64 -output tp_cert temporal_planning.mlb

build_mluntac:
	cd $(MLUNTA_DIR) && make build_checker 

build_muntac:
	cd $(MUNTA_DIR) && make muntac_mlton

build_all: build_tp_conversion build_mluntac build_muntac

tp_to_muntax:
	./tp_cert -domain $(DOMAIN) -problem $(PROBLEM) -output $(OUTPUT)

muntax_to_certificate:
	$(MLUNTAC) -model $(OUTPUT) -certificate $(CERTIFICATE) -renaming $(RENAMING) -extra lu

tp_to_certificate: tp_to_muntax muntax_to_certificate

check_certificate:
	$(MUNTAC) -m $(OUTPUT) -r $(RENAMING) -c $(CERTIFICATE)

compile_check_cert_check: tp_to_certificate check_certificate


