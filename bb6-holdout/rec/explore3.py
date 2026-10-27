from explore import *
def stop2(c): return after_gapstep(c) or at_left_ctx(c)
def show2(name, cfg, stop=stop2):
    try:
        run(cfg, stop)
        print(f"{name}\n   -> {' '.join(map(str, canon(cfg.left)))} {cfg.state}> {' '.join(map(str, canon(cfg.right)))}   steps {cfg.steps}\n    {' '.join(cfg.hist)[:260]}")
    except Halted as e:
        print(f"{name}: HALT ({e}) after {cfg.steps} steps: {' '.join(cfg.hist)}")
    except Exception as e:
        print(f"{name}: EXC {type(e).__name__} {e} at {cfg}  {' '.join(cfg.hist)[-200:]}")
j = Lin("j")
show2("PB-marker", Config(tokens("L 0 1 1 0"), "A", tokens("1 1 R")))
show2("PB-block", Config(tokens("L 0 1 1 1 0"), "A", tokens("1 1 R")))
for nm, Y in [("marker", "1 1 0 R"), ("wall", "0 1 0 R"), ("block", "1 1 1 0 R")]:
    show2("GMW->" + nm, Config(tokens("L 1 0 0"), "E", tokens(f"0 0 (10)^j {Y}", j=j)))
show2("GMW->blank", Config(tokens("L 1 0 0"), "E", tokens("0 0 (10)^j", j=j) + [Blank()]))
show2("GMW->endmarker", Config(tokens("L 1 0 0"), "E", tokens("0 0 (10)^j 1 1", j=j) + [Blank()]))
