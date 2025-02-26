.PHONY: tp_to_muntax

MLUNTA_DIR="../../mlunta"
MLUNTAC:="./$(MLUNTA_DIR)/build/mluntac-mlton"

MUNTA_DIR="../../munta/ML"
MUNTAC:="./$(MUNTA_DIR)/muntac_mlton"

GROUNDER="./../../grounder"

PDDL_DOMAIN?="none"
PDDL_PROBLEM?="none"
DOMAIN?="none"
PROBLEM?="none"
OUTPUT?="none"
CERTIFICATE?="none"
RENAMING?="none"

touch_pd: 
	mkdir -p -- $$(dirname $(PDDL_DOMAIN)) &
	touch $(PDDL_DOMAIN) &
	mkdir -p -- $$(dirname $(PDDL_PROBLEM)) &
	touch $(PDDL_PROBLEM)

ground_problem: touch_pd
	$(GROUNDER) --write-pddl $(DOMAIN) $(PROBLEM) $(PDDL_DOMAIN) $(PDDL_PROBLEM)

build_tp_conversion: 
	mlton -default-type int64 -output tp_cert temporal_planning.mlb

build_mluntac:
	cd $(MLUNTA_DIR) && make build_checker 

build_muntac:
	cd $(MUNTA_DIR) && make muntac_mlton

build_all: | build_tp_conversion build_mluntac build_muntac

touch_o:
	mkdir -p -- $$(dirname "$(OUTPUT)") &
	touch $(OUTPUT)

tp_to_muntax: touch_o
	./tp_cert -domain $(DOMAIN) -problem $(PROBLEM) -output $(OUTPUT)

touch_cert_rnm:
	mkdir -p -- $$(dirname "$(CERTIFICATE)") &
	touch $(CERTIFICATE) &
	mkdir -p -- $$(dirname "$(RENAMING)") &
	touch $(RENAMING)


muntax_to_certificate: touch_cert_rnm
	$(MLUNTAC) -model $(OUTPUT) -certificate $(CERTIFICATE) -renaming $(RENAMING) -extra lu

tp_to_certificate: | tp_to_muntax muntax_to_certificate

check_certificate:
	$(MUNTAC) -m $(OUTPUT) -r $(RENAMING) -c $(CERTIFICATE)

compile_cert_check: | tp_to_certificate check_certificate

ground_compile_cert_check: | ground_problem compile_cert_check

