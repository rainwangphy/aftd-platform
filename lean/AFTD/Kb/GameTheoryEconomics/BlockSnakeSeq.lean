import AFTD.Prelude

/-!
# block_snake_seq

Topic: fair_division   Node: edc75b0fec94

Provenance: formalization of a published result. Source: arXiv:2611.09685, Section 4.1

The block-snake picking sequence for natural numbers n, k, and r with hr : r < n, and draw permutation π : Equiv.Perm (Fin n), defined as a function Fin (k * n + r) → Fin n. For turn m : Fin (k * n + r), if m.val < k * n with round t = m.val / n and offset j = m.val % n: if j < n - r then it gives π of index j (if t is even) or (n - r - 1 - j) (if t is odd); if j ≥ n - r then it gives π of index n - r + (j - (n - r)) (if t is even) or n - r + (r - 1 - (j - (n - r))) (if t is odd). For m.val ≥ k * n with offset j = m.val - k * n, it gives π of index n - r + j (if k is even) or n - r + (r - 1 - j) (if k is odd).
-/

/-- The block-snake sequence for n agents and kn + r objects determined by a draw permutation π. -/
def block_snake_seq (n k r : ℕ) (hr : r < n) (π : Equiv.Perm (Fin n)) :
    Fin (k * n + r) → Fin n := fun m =>
  if ht : m.val < k * n then
    let t := m.val / n
    let j := m.val % n
    if hj : j < n - r then
      π ⟨if t % 2 = 0 then j else n - r - 1 - j, by split_ifs <;> omega⟩
    else
      π ⟨n - r + (if t % 2 = 0 then j - (n - r) else r - 1 - (j - (n - r))), by
        have : m.val % n < n := Nat.mod_lt _ (by omega)
        split_ifs <;> omega⟩
  else
    let j := m.val - k * n
    π ⟨n - r + (if k % 2 = 0 then j else r - 1 - j), by
      have hm := m.isLt
      split_ifs <;> omega⟩
