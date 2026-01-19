show_help () {
  echo "usage:"
  echo "run.sh [args] <domain> <problem> <muntax> <tck> <dot> <rnm>  <cert>"
  echo "-h : help"
  echo "<domain> : ground pddl domain"
  echo "<problem> : ground pddl instance"
  echo "<muntax> : output for muntax model"
  echo "<tck> : output for tck model"
  echo "<dot> : output for tchecker's certificate"
  echo "<rnm> : output for renaming"
  echo "<cert> : output for Munta's certificate"
}

# https://stackoverflow.com/a/14203146

OPTIND=1         # Reset in case getopts has been used previously in the shell.

instances=()
while getopts "h?" opt; do
  case $opt in
    h|\?)
      show_help
      exit 0
      ;;
  esac
done

domain=$1
problem=$2
muntax=$3
tck=$4
dot=$5
renaming=$6
certificate=$7


./ML/out/plan_cert -domain $domain -problem $problem -model $muntax
python -m convert_models.convert $muntax $tck
./tck-reach -a covreach -C graph -s dfs -o $dot $tck
./ML/out/plan_cert -model $muntax -renaming $renaming
 python -m convert_models.convert_certificate -m $muntax $dot $renaming $certificate


msg=$(./muntac -m $muntax -r $renaming -c $certificate)
err=$?
unsolvable_regex=".*Certificate was accepted.*"

if [[ $msg =~ $unsolvable_regex ]]
then
    echo "Problem unsolvable."
else
    echo $msg; exit $err
fi