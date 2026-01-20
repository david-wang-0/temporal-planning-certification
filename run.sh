show_help () {
  echo "usage:"
  echo "run.sh [args] <domain> <problem>"
  echo "-h : help"
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
ts=$(date +%s)
muntax="${problem%.*}_${ts}.muntax"
tck="${problem%.*}_${ts}.tck"
dot="${problem%.*}_${ts}.dot"
renaming="${problem%.*}_${ts}.rnm"
certificate="${problem%.*}_${ts}.cert"


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