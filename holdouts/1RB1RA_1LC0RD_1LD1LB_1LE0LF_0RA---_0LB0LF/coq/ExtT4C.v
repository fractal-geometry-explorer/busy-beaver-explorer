From BusyCoq Require Import T4C.
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "t4ceng" T4C.stepFast T4C.initFastA T4C.initFastB T4C.initFastC T4C.initFastD T4C.fs_size T4C.fs_cells T4C.fs_mode T4C.fs_L T4C.fs_R T4C.runs_pop T4C.r_raw T4C.d_front T4C.d_back T4C.r_tail T4C.fs_list.
