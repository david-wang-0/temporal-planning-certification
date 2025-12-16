create_dirs:
	mkdir -p out/test

clean:
	rm -f out/*

build_certifier: create_dirs
	mlton -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_profile: create_dirs
	mlton -profile time -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb


build_certifier_verbose: create_dirs
	mlton -verbose 2 -inline 700 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_certifier_unsafe: create_dirs
	mlton -const 'MLton.safe false' -verbose 2 -default-type int64 -default-ann 'allowExtendedTextConsts true' -output out/plan_cert plan_cert/src/plan_cert.mlb

build_test: create_dirs
	mlton -output out/test/tests plan_cert/test/tests.mlb

run_test: build_test
	./out/test/tests