"""1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE: lean/Macro.lean `mstep`, `halts_iff_mstep` (and `halts_iff`)."""

MACHINE = "1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE"
LEAN = ("holdouts/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE/lean/Macro.lean: mstep, M0, halts_iff_mstep "
        "(epoch form: g, seq, nextWall, epochs, halts_iff)")
VARS = ("a", "K", "j")
START = (3, 0, 1)
HALT = "a = 0 and K even"
KIND = "parity-3/2"
BOUND = ("3 epochs (walls 3, 25, 227097; 227,128 phases, ~1e79981 steps), epoch 3 odd by native_decide "
         "(lean/Epoch3.lean epoch3_odd, halts_late); epoch 4 wall has 39,991 digits")


def step(s):
    a, K, j = s
    J = j + 3 * (K // 2)
    if K % 2 == 0:
        if a == 0:
            return None, "H"
        return (a - 1, J + 1, 0), "even"
    if a == 0:
        return (2 * J + 7, 0, 1), "reset"
    return (a - 1, J + 3, 1), "odd"
