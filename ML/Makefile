create_dirs:
	mkdir -p out/test

clean:
	rm -f out/*

build_certifier: create_dirs
	mlton -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_verbose: create_dirs
	mlton -verbose 2 -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_unsafe: create_dirs
	mlton -const 'MLton.safe false' -verbose 2 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_diag: create_dirs
	~/stuff/mlton/build/bin/mlton  -const 'MLton.safe false' -verbose 2 -keep ssa -keep ssa2 -keep sxml -keep xml -keep core-ml -keep ast -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb >> output.txt

build_certifier_diag_safe: create_dirs
	~/stuff/mlton/build/bin/mlton -verbose 2 -keep ssa -keep ssa2 -keep sxml -keep xml -keep core-ml -keep ast -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb >> output.txt

build_certifier_sxml: create_dirs
	mlton -verbose 2 -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert.sxml

build_certifier_ssa: create_dirs
	mlton -verbose 2 -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert.ssa

run_blocks_prob:
	./out/plan_cert -domain ../examples/blocks-world/ground-blocks-2.pddl -problem ../examples/blocks-world/ground-blocks-prob-2.pddl -certificate ../examples/blocks-world/blocks-2.cert -renaming ../examples/blocks-world/blocks-2.rnm -mode 2 -extra lu -show-cert 1

run_trucks_prob:
	./out/plan_cert -domain ../examples/trucks-time/domain.pddl -problem ../examples/trucks-time/instance-2.pddl -certificate ../examples/trucks-time/instance-2.cert -renaming ../examples/trucks-time/instance-2.rnm -mode 2 -extra lu -show-cert 1

	
build_test: create_dirs
	mlton -output out/test/tests plan_cert/test/tests.mlb

run_test: build_test
	./out/test/tests