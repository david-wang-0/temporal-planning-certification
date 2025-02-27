dir=$1
domain=$2
instance=$3
instance_dir=$(dirname $instance)
instance_basename=$(basename $instance)
instance_name="${instance_basename%.*}"

make -C ML ground_compile_cert_check \
    PDDL_DOMAIN=../$dir/$domain \
    PDDL_PROBLEM=../$dir/$instance \
    GROUND_DOMAIN=../$dir/out/ground_domain_$instance_name.pddl \
    GROUND_PROBLEM=../$dir/out/ground_problem_$instance_name.pddl \
    OUTPUT=../$dir/out/$instance_name.muntax \
    CERTIFICATE=../$dir/out/$instance_name.cert \
    RENAMING=../$dir/out/$instance_name.rnm