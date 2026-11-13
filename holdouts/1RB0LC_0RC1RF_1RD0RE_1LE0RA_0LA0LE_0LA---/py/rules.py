import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '../../1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0LC---/py'))
from family import lean_rules  # noqa: E402

M = os.path.basename(os.path.dirname(HERE))
NS = open(os.path.join(HERE, '../lean/Machine.lean')).read().split('namespace ')[1].split()[0]
text = lean_rules(M, NS)
if len(sys.argv) > 1:
    open(sys.argv[1], 'w').write(text)
else:
    print(text)
