# Sources MLton compiles into the certifier: plan_cert's own sources, the code exported from
# Isabelle (Check_Unsolvability.ML, pulled in via converter.mlb) and the vendored libraries.
# Listed so `make` rebuilds out/plan_cert whenever any of them changes (MLton tracks its own
# internal dependency graph, but make needs the prerequisites to know when to re-invoke it).
CERT_SRCS := $(shell find plan_cert/src plan_cert/imports lib \( -name '*.sml' -o -name '*.sig' -o -name '*.fun' -o -name '*.mlb' -o -name '*.ML' \) 2>/dev/null) \
             Check_Unsolvability.ML converter.mlb term_stub.sml
MLTON_FLAGS := -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true'

.PHONY: create_dirs clean build_certifier build_certifier_profile \
        build_certifier_verbose build_certifier_unsafe build_test run_test

create_dirs:
	mkdir -p out/test

clean:
	rm -f out/*

# File target: rebuilds only when a source changed (or the binary is missing).
out/plan_cert: $(CERT_SRCS)
	mkdir -p out
	mlton $(MLTON_FLAGS) -output out/plan_cert plan_cert/src/plan_cert.mlb

# Convenience alias (kept for existing callers / scripts).
build_certifier: out/plan_cert

build_certifier_profile: create_dirs
	mlton -profile time $(MLTON_FLAGS) -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_verbose: create_dirs
	mlton -verbose 2 $(MLTON_FLAGS) -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_unsafe: create_dirs
	mlton -const 'MLton.safe false' -verbose 2 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_test: create_dirs
	mlton -output out/test/tests plan_cert/test/tests.mlb

run_test: build_test
	./out/test/tests
