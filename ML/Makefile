.PHONY: tp_to_muntax

MLUNTA_DIR="../../mlunta"
MLUNTAC:="./$(MLUNTA_DIR)/build/mluntac-mlton"

MUNTA_DIR="../../munta_2025/ML"
MUNTAC:="./$(MUNTA_DIR)/muntac_mlton"

GROUNDER="./../../grounder"

PDDL_DOMAIN?="none"
PDDL_PROBLEM?="none"
GROUND_DOMAIN?="none"
GROUND_PROBLEM?="none"
OUTPUT?="none"
CERTIFICATE?="none"
RENAMING?="none"

mk_dir_pd:
	mkdir -p -- $$(dirname $(GROUND_DOMAIN)) 
	mkdir -p -- $$(dirname $(GROUND_PROBLEM))

touch_pd: mk_dir_pd
	touch $(GROUND_DOMAIN)
	touch $(GROUND_PROBLEM)

ground_dom_and_prob: mk_dir_pd
	$(GROUNDER) --write-pddl $(GROUND_DOMAIN) $(GROUND_PROBLEM) $(PDDL_DOMAIN) $(PDDL_PROBLEM)

build_tp_conversion: 
	mlton -default-type int64 -output tp_cert temporal_planning.mlb

build_mluntac:
	cd $(MLUNTA_DIR) && make build_checker 

build_muntac:
	cd $(MUNTA_DIR) && make muntac_mlton

build_all: | build_tp_conversion build_mluntac build_muntac

mk_dir_o:
	mkdir -p -- $$(dirname "$(OUTPUT)") 

touch_o: mk_dir_o
	touch $(OUTPUT)

tp_to_muntax: mk_dir_o
	./tp_cert -domain $(GROUND_DOMAIN) -problem $(GROUND_PROBLEM) -output $(OUTPUT)

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

ground_compile_cert_check: | ground_dom_and_prob compile_cert_check

