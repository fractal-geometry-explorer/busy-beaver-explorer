"""Build and run the family's C simulators (c/rl.c, c/direct.c of the family lead) for any of the sixteen machines."""
import os
import subprocess
import sys
import tempfile

LEADDIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_bin = {}


def build(name):
    if name not in _bin:
        out = os.path.join(tempfile.gettempdir(), f'g04_{name}_{os.getpid()}')
        subprocess.run(['gcc', '-O2', '-o', out, os.path.join(LEADDIR, 'c', name + '.c')], check=True)
        _bin[name] = out
    return _bin[name]


def orientation(M):
    """(side, sweep-end state, background word) of the rl.c call for M."""
    if M.startswith('1RB0LC_0RC0RB_1LD0RE_0LE'):
        return 'R', 'E', '0010'
    return 'L', 'C', '0100'


def rl(M, steps, every=1, quiet_f=False, nocross=False):
    """The output lines of rl.c for M."""
    side, st, P = orientation(M)
    env = dict(os.environ)
    if nocross:
        env['RL_NOCROSS'] = '1'
    r = subprocess.run([build('rl'), M, str(steps), side, st, P, str(every), '0', 'F', '1' if quiet_f else '0'],
                       capture_output=True, text=True, env=env, check=True)
    return r.stdout.splitlines()


def direct(M, steps):
    r = subprocess.run([build('direct'), M, str(int(float(steps)))], capture_output=True, text=True, check=True)
    return r.stdout.splitlines()


if __name__ == '__main__':
    for line in rl(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 0):
        print(line)
