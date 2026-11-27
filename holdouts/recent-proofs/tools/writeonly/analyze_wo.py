# Lists the ends of wotest-screen-nov27.tsv with the strict signature: a saturated set of keys, at least two
# return states, a return state fixed by the key and at most 8 cells, trips of more than 20 steps per cell.
# Usage: python3 analyze_wo.py wotest-screen-nov27.tsv
import sys, csv
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
seen = set()
for r in rows:
    k = (r['machine'], r['end'])
    if k in seen: continue
    deep = int(r['deep_trips']); keys = [int(x) for x in r['keys_by_quarter'].split(',')]
    if deep < 50 or keys[1] != keys[3] or len(r['return_states']) < 2 or float(r['dur_per_depth']) < 20: continue
    if int(r['amb_K8']) != 0: continue
    seen.add(k)
    print(r['machine'], r['end'], 'W=' + r['W'], 'tape=' + r['tape'], 'deep=' + r['deep_trips'], 'keys=' + str(keys[3]),
          'return=' + r['return_states'], 'ambiguous_K0=' + r['amb_K0'], 'steps_per_cell=' + r['dur_per_depth'])
print(len(seen), 'ends')
