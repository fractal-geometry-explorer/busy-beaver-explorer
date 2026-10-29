Outputs of long runs (see ../notes/LAB_NOTES.md for how each was made).

- `left_records_1e10.txt`: every step up to 10¹⁰ at which the head reaches a cell left of all earlier ones, with the
  tape (lines cut at 200 characters), and the final line of the run:
  `tools/c/tmrun 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB 10000000000 records 100000000 | awk '$2=="L" || /running|halted/ {print substr($0,1,200)}'`
  (about a minute).
