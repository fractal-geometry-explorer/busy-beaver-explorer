import Replay
import Return74

/-!
`replay` (`Replay.lean`) with the kernel bound below 2^74 (`no_one_1e22_kernel`): for every a = 1 + 2^m u, with no
upper bound on a, the first min(m, 3·2^72 + 2) passes of the excursion from `[a, 2a+1]` never halt and never stop at
a block of 1. Kernel only; checked by `check_return74.sh` after `Return74.lean`.
-/

namespace BB6d

theorem replay_1e22_kernel (m u t : Nat) (hm : 1 ≤ m) (hu : 1 ≤ u) (ht : t + 1 ≤ m) (hb : t ≤ 3 * 2 ^ 72 + 1) :
    ∃ ys, iter (t + 1) [2 * (1 + 2 ^ m * u) + 1, 1 + 2 ^ m * u] = .ok ys := by
  obtain ⟨zs, _, h, _⟩ := no_one_1e22_kernel t hb
  obtain ⟨ys, hy, _⟩ := replay m u t hm hu ht zs h
  exact ⟨ys, hy⟩

end BB6d
