import AFTD.Prelude

/-!
# simple_graph_cycle_power

Topic: combinatorics   Node: 0d8cc664821b

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Sec. 1 (definition of the k-th power of a cycle).

The k-th power C_n^k of the cycle C_n: vertices are the residues mod n, and two distinct vertices are adjacent when their distance along the cycle, min((u - v) mod n, (v - u) mod n), is at most k.
-/

/-- The `k`-th power `C_n^k` of the `n`-cycle on `ZMod n`: distinct `u, v` are adjacent iff their cyclic distance `min ((u - v).val) ((v - u).val)` is at most `k`. -/
def simple_graph_cycle_power (n k : ℕ) : SimpleGraph (ZMod n) where
  Adj u v := u ≠ v ∧ min (u - v).val (v - u).val ≤ k
  symm := ⟨fun (u v : ZMod n) (h : u ≠ v ∧ min (u - v).val (v - u).val ≤ k) =>
    ⟨h.1.symm, by rw [min_comm]; exact h.2⟩⟩
  loopless := ⟨fun (u : ZMod n) (h : u ≠ u ∧ min (u - u).val (u - u).val ≤ k) => h.1 rfl⟩
