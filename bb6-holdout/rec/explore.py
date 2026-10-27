from symtm import *
def after_gapstep(c): return c.state == "E" and len(c.hist) >= 2 and c.hist[-1] == "A1" and c.hist[-2] in ("B1", "[A0 B1]x1")
def at_left_ctx(c): return canon(c.left) and isinstance(canon(c.left)[-1], Ctx) and len(canon(c.left)) == 1
def show(name, L, st, R, stop, **v):
    c = Config(tokens(L, **v), st, tokens(R, **v))
    try:
        run(c, stop)
        print(f"{name}: {L} {st}> {R}\n   -> {' '.join(map(str, canon(c.left)))} {c.state}> {' '.join(map(str, canon(c.right)))}   steps {c.steps}")
        print("   ", " ".join(c.hist)[:300])
    except Exception as e:
        print(f"{name}: EXC {type(e).__name__} {e}  at  {c}  hist {' '.join(c.hist)[-200:]}")
    return c
m = Lin("m")
show("BOUNCE", "L 0 0", "E", "0 (10)^m+2 1 1 0 R", after_gapstep, m=m+2)
show("SWAP", "L 1 0 0", "E", "0 1 1 0 R", after_gapstep)
show("MERGE", "L 1 0 0", "E", "0 1 0 1 1 0 R", at_left_ctx)
show("WALLBOUNCE", "L 0 0", "E", "0 (10)^m+1 0 R", after_gapstep, m=m+1)
