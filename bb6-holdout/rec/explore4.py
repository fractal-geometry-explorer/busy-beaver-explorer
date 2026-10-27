from explore3 import *
def stop_A_left(c): return c.state == "A" and at_left_ctx(c)
def after_shift_pass(c): return c.state == "E" and len(c.hist) >= 2 and c.hist[-1] == "A1" and c.hist[-2].startswith("[A0 B1]")
j, m = Lin("j"), Lin("m")
print("=== PB-marker"); show2("PB-marker", Config(tokens("L 1 0 1 1 0"), "A", tokens("1 1 R")), stop_A_left)
print("=== GMW->marker"); show2("GMW->marker", Config(tokens("L 1 0 0"), "E", tokens("0 0 (10)^j 1 1 0 R", j=j)), after_shift_pass)
for nm, Y in [("marker", "1 1 0 R"), ("wall", "0 1 0 R"), ("block", "1 1 1 0 R")]:
    stop = after_shift_pass if nm == "marker" else stop2
    show2("PASSBLOCK->" + nm, Config(tokens("L 1 0 0"), "E", tokens(f"0 (10)^m 1 1 1 0 (10)^j {Y}", m=m, j=j)), stop)
show2("PASSBLOCK->blank", Config(tokens("L 1 0 0"), "E", tokens("0 (10)^m 1 1 1 0 (10)^j", m=m, j=j) + [Blank()]))
show2("PASSBLOCK->endmarker", Config(tokens("L 1 0 0"), "E", tokens("0 (10)^m 1 1 1 0 (10)^j 1 1", m=m, j=j) + [Blank()]))
