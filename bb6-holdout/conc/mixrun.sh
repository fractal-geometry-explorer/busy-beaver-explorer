#!/bin/bash
# usage: mixrun.sh WORD K
python3 mixsolve.py $1 $2 2>&1 | python3 -c "
import sys
for l in sys.stdin:
    if l.startswith('point'): print('   ', l[l.index('rel.'):].strip()[:160])
    elif l.startswith('  halv'):
        v = eval(l.split(':',1)[1]); print('    meetings', len(v), 'max halvings', max(v) if v else None)
    elif l.startswith('word'): print(l.strip()[l.index(':')-0:][:200] if len(l)>200 else l.strip())
    else: print('   ', l.strip())
"
