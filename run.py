from convert_models.convert_certificate import convert_from_files
import json
import argparse
import os
from os.path import join, isfile
import subprocess
from itertools import chain, tee
import sys
import pprint
import re


def find_certificates(folders, patterns):
    def get_from_pattern(filename, pattern):
        if filename.endswith(pattern):
            cert_name = filename[:-4]
            return filename[:-len(pattern)], cert_name
        return None

    def get_from_file(filename):
        for pattern in patterns:
            x = get_from_pattern(filename, pattern)
            if x != None:
                return x
        return None

    result = {}
    for folder in folders:
        for root, dirs, files in os.walk(folder):
            for file in files:
                x = get_from_file(file)
                if x != None:
                    name, cert_name = x
                    pair = name, root
                    if pair not in result:
                        result[pair] = []
                    result[pair].append((join(root, file), cert_name))
    return result


def convert_certificate(cert_name, name, path, filename, is_imi, is_buechi=True, overwrite=False):
    model = join(path, name + ".muntax")
    renaming = join(path, name + ".renaming")
    cert = join(path, cert_name + ".cert")
    if not isfile(model):
        raise ValueError("Model does not exist: " + model)
    if not isfile(renaming):
        raise ValueError("Renaming does not exist: " + renaming)
    if overwrite or not isfile(cert):
        try:
            nums, binary = convert_from_files(filename, renaming, is_buechi=is_buechi, compute_nums=(
                not is_imi), is_imitator=is_imi, ignore_vars=is_imi, model_file=None if is_imi else model)
        except Exception as e:
            print("Error while converting: " + filename)
            raise e
        with open(cert, 'wb') as f:
            f.write(binary)
        return nums


def check_certificate(cert_name, name, path, is_buechi=True):
    model = join(path, name + ".muntax")
    renaming = join(path, name + ".renaming")
    certificate = join(path, cert_name + ".cert")
    munta = ["munta/ML/muntac_mlton", "-m",
             model, "-r", renaming, "-c", certificate]
    if is_buechi:
        munta += ["-i", "4"]
    else:
        munta += ["-i", "3"]
    print(" ".join(munta))
    cp = subprocess.run(munta, universal_newlines=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout = str(cp.stdout)
    if "Certificate was rejected" in stdout:
        return False, stdout
    elif "Certificate was accepted" in stdout:
        return True, stdout
    else:
        print("No verdict for: " + certificate)
        print("")
        print(stdout)
        raise ValueError("No verdict for: " + certificate)


time_re = re.compile("(Time for | Time to )([ \w]+): ([0-9]+\.[0-9]+)")


def read_times_from_log(log):
    times = {}
    for line in log.split("\n"):
        match = time_re.match(line)
        if match == None:
            continue
        _, name, time = match.groups()
        if name in times:
            raise ValueError("Duplicate timings!")
        times[name] = float(time)
    if "certificate checking" not in times:
        raise ValueError("No certificate checking time found in log!")
    return times


def mk_latex_table(imi_certificates, tchecker_certificates, db):
    logs = db['logs']
    numbers = db['numbers']
    models = [model for model, folder in tchecker_certificates]

    def model_to_name(name):
        return name
    ident_patterns = [
        "merge",
        "incl",
        "ndfssub",
        "ndfs",
        "fsttcs16-bad",
        "fsttcs"
    ]

    def make_entry(pair):
        filename, ident = pair
        for pattern in ident_patterns:
            if pattern in ident:
                ident = pattern
                break
        verdict, log = logs[filename]
        times = read_times_from_log(log)
        time = times["certificate checking"]
        nums = numbers[filename]
        locs, dbms, edges = nums
        verdict = r"\Y" if verdict else r"\N"
        entry = f"{verdict} & {dbms:6} & {time:6.2f}"
        return ident, entry

    tchecker_entries = {}
    for (model, _), certs in tchecker_certificates.items():
        entries = {}
        for cert in certs:
            ident, entry = make_entry(cert)
            entries[ident] = entry
        tchecker_entries[model] = entries

    imi_entries = {}
    for (model, _), certs in imi_certificates.items():
        entries = {}
        for cert in certs:
            ident, entry = make_entry(cert)
            entries[ident] = entry
        imi_entries[model] = entries

    lines = []
    for model in sorted(models):
        name = model.upper()
        tchecker_ndfs = tchecker_entries[model]['ndfs']
        tchecker_scc = tchecker_entries[model]['fsttcs']
        default_entry = "\multicolumn{3}{c}{***}"
        imi_merge = imi_entries[model]['merge'] if model in imi_entries and 'merge' in imi_entries[model] else default_entry
        imi_ndfs = imi_entries[model]['ndfssub'] if model in imi_entries and 'ndfssub' in imi_entries[model] else default_entry
        parts = [name, "", tchecker_scc, "",
                 tchecker_ndfs, "", imi_merge, "", imi_ndfs]
        lines.append(" & ".join(parts))

    return " \\\\\n".join(lines) + "\\\\"


def do_it(db_path, report, reachability, skip_tchecker, mk_certs, mk_run, models, overwrite=False):
    with open(db_path) as db_file:
        db = json.load(db_file)

    try:
        imi_certificates = find_certificates(
            db["imi-folders"], db["imi-patterns"])
        for model_folder in db['imi-ignore']:
            del imi_certificates[tuple(model_folder)]
        tchecker_certificates = find_certificates(
            db["tchecker-folders"], db["tchecker-patterns"])
        pp = pprint.PrettyPrinter(indent=2)
        print("The following models and certificates have been identified")
        print("\nImitator:")
        pp.pprint(imi_certificates)
        print("\nTChecker:")
        pp.pprint(tchecker_certificates)
        print("")
        if models == []:
            models = [name for name, _ in tchecker_certificates.keys()]
        tchecker_iter = () if skip_tchecker else ((x, False)
                                                  for x in tchecker_certificates.items())
        all_items, all_items2 = tee(
            chain(tchecker_iter, ((x, True) for x in imi_certificates.items())))
        paths = dict(tchecker_certificates.keys())
        if mk_certs:
            numbers = db['numbers']
            for ((name, path), certs), is_imi in all_items:
                if name in models:
                    if is_imi:
                        path = paths[name]
                    for filename, cert_name in certs:
                        nums = convert_certificate(
                            cert_name, name, path, filename, is_imi, not reachability, overwrite)
                        if nums != None:
                            numbers[filename] = nums

        if mk_run:
            logs = db['logs']
            for ((name, path), certs), is_imi in all_items2:
                if name in models:
                    if is_imi:
                        path = paths[name]
                    for filename, cert_name in certs:
                        if not overwrite and filename in logs:
                            continue
                        verdict, log = check_certificate(
                            cert_name, name, path, not reachability)
                        print("{}: {}".format(
                            cert_name, "accepted" if verdict else "rejected"))
                        logs[filename] = verdict, log
    finally:
        if report:
            for filename, (verdict, _) in db['logs'].items():
                print("{}: {}".format(
                    filename, "accepted" if verdict else "rejected"))
            table = mk_latex_table(imi_certificates, tchecker_certificates, db)
            print()
            print(table)
        with open(db_path, 'w') as db_file:
            json.dump(db, db_file, indent=4)


parser = argparse.ArgumentParser(
    description="Convert certificates and run certificate checker.")
parser.add_argument(
    "--report", action='store_true', help="Report current database entries.")
parser.add_argument(
    "--certificates", action='store_true', help="Convert certificates")
parser.add_argument(
    "--check", action='store_true', help="Check certificates")
parser.add_argument(
    "--reach", action='store_true', help="Produce and check reachability certificates")
parser.add_argument(
    "--skip-tchecker", action='store_true', help="Skip TChecker files.")
parser.add_argument("--overwrite", action='store_true',
                    help="Overwrite existing files [NOT SAFE, some files may always be overwritten!]")
parser.add_argument(
    "--all", action='store_true', help="Run all models")
parser.add_argument('models', metavar='N', type=str, nargs='*',
                    help='Names of the models that should be run.')

if __name__ == "__main__":
    args = parser.parse_args()
    if not any((args.report, args.certificates, args.check)):
        print("You need to specify at least one flag!")
        parser.print_usage()
        sys.exit(0)
    if not args.models and not args.all and any((args.certificates, args.check)):
        print("You either need to specify at least one model or --all")
        parser.print_usage()
        sys.exit(0)
    do_it("db.json", args.report, args.reach, args.skip_tchecker, args.certificates,
          args.check, args.models, args.overwrite)
