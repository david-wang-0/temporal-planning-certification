ground_example () {
    local pddl_dir=$1
    local instance_name=$2
    local out_dir=$3

    local out_domain="$out_dir/$instance_name-domain.pddl"
    local out_problem="$out_dir/$instance_name-problem.pddl"

    local in_domain="$pddl_dir/domain.pddl"
    local in_problem="$pddl_dir/instances/$instance_name.pddl"
    ../grounder --write-pddl $out_domain $out_problem $in_domain $in_problem
}

convert_to_muntax () {
    local out_dir=$1
    local instance_name=$2

    local out_domain="$out_dir/$instance_name-domain.pddl"
    local out_problem="$out_dir/$instance_name-problem.pddl"

    local out_model="$out_dir/$instance_name.muntax"

    ./ML/out/plan_cert -domain $out_domain -problem $out_problem -model $out_model
}

rename () {
    local out_dir=$1
    local instance_name=$2

    local out_model="$out_dir/$instance_name.muntax"
    local out_rnm="$out_dir/$instance_name.rnm"

    ./ML/out/plan_cert -model $out_model -renaming $out_rnm
}

run_example () {
    local out_dir=$1
    local instance_name=$2

    local out_domain="$out_dir/$instance_name-domain.pddl"
    local out_problem="$out_dir/$instance_name-problem.pddl"

    local out_model="$out_dir/$instance_name.muntax"
    local out_cert="$out_dir/$instance_name.cert"
    local out_rnm="$out_dir/$instance_name.rnm"

    ./ML/out/plan_cert -domain $out_domain -problem $out_problem -model $out_model -renaming $out_rnm -certificate $out_cert -extra lu -mode 2 -certify 1
}

# https://stackoverflow.com/a/14203146

OPTIND=1         # Reset in case getopts has been used previously in the shell.

# Initialize our own variables:
ground=false
run=false
rename=false

while getopts "h?grRp:" opt; do
  case "$opt" in
    h|\?)
      show_help
      exit 0
      ;;
    g) ground=true
      ;;
    r) run=true
      ;;
    R) rename=true
      ;;
    p) in_dir=$OPTARG
      ;;
  esac
done

shift $((OPTIND-1))

out_dir=$1
instance=$2

if [ -z ${out_dir+x} ]
then
    echo "No folder for ground PDDL and output specified"
    exit 1
fi


if [ -z ${instance+x} ]
then
    echo "No instance specified"
    exit 1
fi

if [ $ground = true ]
then
    if [ -z ${in_dir+x} ]
    then
        echo "No folder for PDDL files specified."
        exit 1
    else 
        ground_example $in_dir $instance $out_dir
    fi
fi

if [ $run = true ]
then
  run_example $out_dir $instance
elif [ $rename = true ]
then
  rename $out_dir $instance
  echo "rename"
else
  convert_to_muntax $out_dir $instance
fi