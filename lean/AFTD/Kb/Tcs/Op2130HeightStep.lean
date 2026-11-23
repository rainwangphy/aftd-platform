import AFTD.Prelude

/-!
# op2130_height_step

Topic: online_algorithms   Node: 45b3b81eac3c

Provenance: helper lemma. OP-2130, path cumulative heights

One greedy update of a path cumulative-height profile at an interior site, using the supplied coin for a tie.
-/

def op2130_height_step (h : ℕ → ℤ) (p : ℕ) (coin : Bool) : ℕ → ℤ := Function.update h p (h p +
    if 2 * h p < h (p - 1) + h (p + 1) then 1
    else if h (p - 1) + h (p + 1) < 2 * h p then -1
    else if coin then 1 else -1)
