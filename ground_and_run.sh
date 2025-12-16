ground_example () {
    local pddl_dir=$1
    local instance_name=$2
    local out_dir=$3

    local out_domain=$out_dir/$instance_name-domain.pddl
    local out_problem=$out_dir/$instance_name-problem.pddl

    local in_domain=$pddl_dir/domain.pddl
    local in_problem=$pddl_dir/instances/$instance_name.pddl
    ../grounder --write-pddl $out_domain $out_problem $in_domain $in_problem
}

run_example () {
    local out_dir=$1
    local instance_name=$2

    local out_domain=$out_dir/$instance_name-domain.pddl
    local out_problem=$out_dir/$instance_name-problem.pddl

    local out_model=$out_dir/$instance_name.muntax
    local out_cert=$out_dir/$instance_name.cert
    local out_rnm=$out_dir/$instance_name.rnm

    ./ML/out/plan_cert -domain $out_domain -problem $out_problem -model $out_model -renaming $out_rnm -certificate $out_cert -extra lu -mode 2 -certify 1
}

in_dir=$1
instance_name=$2
out_dir=$3

ground_example $in_dir $instance_name $out_dir

run_example $out_dir $instance_name