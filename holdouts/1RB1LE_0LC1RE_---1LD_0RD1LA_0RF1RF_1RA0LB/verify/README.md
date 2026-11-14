# Independent re-computation of the halt

Written separately from `../py/accel.py` to check its result. Only the 16-position level table is taken from the
machine's README; the step constants are measured again by `measure.py`. Run from this folder:

```sh
gcc -O2 -o sim sim.c && gcc -O2 -o sim2 sim2.c    # two direct simulators (plain, and on 16-cell blocks)
python3 measure.py          # measures the step constants of every level position, writes const.json
python3 myrun.py 1          # the level odometer from visit 3040 to the last visit, writes final_keep1.pkl
python3 final.py final_keep1.pkl    # the last visit; compares the halting step with ../halt.txt and ../README.md
python3 myrun.py 1 3040 1e10        # optional: model against the direct run at every checkpoint up to 1e10 steps
```

`lib.py` holds the tape/digit conversions and the call to `sim`; `mymodel.py` is the model; `const.json` is the
output of `measure.py` as committed. The binaries and `final_keep1.pkl` are not committed.
