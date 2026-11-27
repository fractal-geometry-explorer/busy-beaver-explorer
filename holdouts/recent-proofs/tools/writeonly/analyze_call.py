# Lists the directions of calltest-screen-nov27.tsv where deep trips return a state fixed by 16 cells:
# at least 1000 deep trips, two or more return states, more than 2% ambiguous at K = 4, at most 0.1% at K = 16
# with at most 2000 classes, and at least 8 steps per cell of depth.
# Usage: python3 analyze_call.py calltest-screen-nov27.tsv
import sys, csv
n = 0
rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
for r in sorted(rows, key=lambda r: -float(r['dur_per_depth'])):
    if int(r['deep_trips']) < 1000 or len(r['return_states']) < 2 or float(r['dur_per_depth']) < 8: continue
    if float(r['amb_K16']) > 0.001 or int(r['keys_K16']) > 2000 or float(r['amb_K4']) <= 0.02: continue
    n += 1
    print(r['machine'], r['direction'], 'steps_per_cell=' + r['dur_per_depth'], 'return=' + r['return_states'],
          'K4=' + r['amb_K4'], 'K8=' + r['amb_K8'], 'K16=' + r['amb_K16'], 'keys16=' + r['keys_K16'])
print(n, 'directions')
