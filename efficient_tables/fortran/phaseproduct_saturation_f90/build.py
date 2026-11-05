"""Build the Fortran90 executable; no numerical search is performed here."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def build(debug=False, compiler=None):
    fc = compiler or os.environ.get('FC')
    if fc and not os.path.dirname(fc):
        name = fc
        fc = shutil.which(name)
        if not fc:
            raise SystemExit(f'GNU Fortran compiler {name!r} was not found on PATH.')
    if not fc:
        fc = shutil.which('gfortran')
    if not fc:
        raise SystemExit('Set FC to a GNU Fortran compiler or pass --compiler.')
    fc = str(Path(fc).resolve())
    out = ROOT / 'build' / ('debug' if debug else 'release')
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['PATH'] = str(Path(fc).parent) + os.pathsep + env.get('PATH', '')
    flags = ['-std=f95', '-pedantic', '-Wall', '-Wextra', '-Wimplicit-interface', '-Werror=line-truncation']
    flags += ['-O0', '-g', '-fcheck=all', '-fbacktrace', '-ftrapv'] if debug else ['-O3']
    sources = ['sp_arithmetic.f90', 'sp_rational.f90', 'sp_lattice.f90', 'sp_ilp.f90',
               'sp_oracle.f90', 'sp_threshold.f90', 'sp_outer.f90', 'sp_main.f90']
    exe = out / ('phaseproduct_saturation.exe' if os.name == 'nt' else 'phaseproduct_saturation')
    command = [fc, *flags, '-J', str(out), '-I', str(out)]
    command += [str(ROOT / 'src' / name) for name in sources]
    if sys.platform != 'darwin':
        command.append('-static')
    command += ['-o', str(exe)]
    subprocess.run(command, cwd=out, env=env, check=True)
    (out / 'command.txt').write_text(subprocess.list2cmdline(command) + '\n')
    manifest={'command':command,
              'compiler_version':subprocess.check_output([fc,'--version'],env=env,text=True).splitlines()[0],
              'executable_sha256':hashlib.sha256(exe.read_bytes()).hexdigest(),
              'sources':{name:hashlib.sha256((ROOT/'src'/name).read_bytes()).hexdigest() for name in sources}}
    (out/'build_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return exe


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--debug', action='store_true')
    parser.add_argument('--compiler')
    args = parser.parse_args()
    print(build(args.debug, args.compiler))
