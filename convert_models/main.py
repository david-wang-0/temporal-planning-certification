from .convert import convert_from_file
from .convert_certificate import convert_from_renaming_file
import subprocess
import sys
import json

usage_string = "Usage: convert.py [-b] model renaming output_file"

if __name__ == "__main__":
    if len(sys.argv) not in [4, 5]:
        print("Usage: convert.py model renaming output_file")
        sys.exit(0)
    files = sys.argv[1:4]
    is_buechi = False
    if len(sys.argv) == 5:
        files = sys.argv[2:5]
        if sys.argv[1] in ["-b", "-buechi", "--buechi"]:
            is_buechi = True
        else:
            print("Unrecognized option: ", sys.argv[1])
            print(usage_string)
            sys.exit(0)
    model_file, renaming_file, output_file = files
    try:
        certificate = convert_from_file(model_file)
    except json.decoder.JSONDecodeError as e:
        print("Error while reading model!", file=sys.stderr)
        raise e
    except Exception as e:
        print("Error while converting certificate to model!", file=sys.stderr)
        raise e
    import os
    temp_dot_file = "temp.dot"
    mode = "zg:elapsed:extraMg"
    target = "_NO_REACH_"
    # binary overridable via env (it is often installed as `tck-reach`, or off PATH)
    tchecker_bin = os.environ.get("TCHECKER_BIN", "tchecker")
    tchecker = [tchecker_bin, "covreach", "-m", mode, "-S",
                "-l", target, "-f", "dot", "-o", temp_dot_file]
    try:
        cp = subprocess.run(tchecker, input=certificate, encoding='ascii')
    except FileNotFoundError as e:
        print("tchecker binary not found: %s (set TCHECKER_BIN)" % tchecker_bin,
              file=sys.stderr)
        sys.exit(2)
    if cp.returncode != 0:
        print("tchecker exited with status %d" % cp.returncode, file=sys.stderr)
        sys.exit(cp.returncode)
    with open(temp_dot_file, 'r') as certificate_file:
        certificate = certificate_file.readlines()
        binary = convert_from_renaming_file(
            certificate, renaming_file, is_buechi)
        with open(output_file, 'wb') as output_file:
            output_file.write(binary)
