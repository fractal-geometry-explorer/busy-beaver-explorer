From BusyCoq Require Import T4C.
Require Extraction.
Extraction Language OCaml.
Extraction "t4ceng.ml" T4C.stepFast T4C.initFastC T4C.fs_mode T4C.fs_L T4C.fs_R T4C.fs_list T4C.fs_size T4C.fs_cells T4C.initFastA T4C.initFastB T4C.initFastD.
