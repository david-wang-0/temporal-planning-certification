create_dirs:
	mkdir -p out

clean:
	rm -f out/*

build_certifier: create_dirs
	mlton -verbose 2 -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

run_blocks_prob: build_certifier
	./out/plan_cert -domain ../examples/blocks-world/ground-blocks-2.pddl -problem ../examples/blocks-world/ground-blocks-prob-2.pddl -certificate ../examples/blocks-world/blocks-2.cert -renaming ../examples/blocks-world/blocks-2.rnm -mode 3 -extra lu -show-cert
