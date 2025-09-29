create_dirs:
	mkdir -p out

clean:
	rm -f out/*

build_certifier: create_dirs
	mlton -mlb-path-map paths.mlb -cc-opt -O3 -cc-opt -g0 -output out/plan_cert plan_cert/src/plan_cert.mlb