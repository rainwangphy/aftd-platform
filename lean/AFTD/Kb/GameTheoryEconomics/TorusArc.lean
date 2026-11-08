import AFTD.Prelude

/-!
# torusArc

Topic: combinatorial_games   Node: 277fa9758ef6

Provenance: helper lemma. step towards three_by_cycle_torus_moving_target_accuracy_exact

The set of all vertices of the 3-by-n torus lying in the L consecutive columns a, a+1, ..., a+L-1 (column indices taken mod n).
-/

/-- A contiguous band of L columns of the 3-by-n torus, starting at column a (mod n). -/
def torusArc (n a L : ℕ) : Finset (Fin 3 × Fin n) := if h : 0 < n then
    (Finset.range L).biUnion
      (fun i => (Finset.univ : Finset (Fin 3)).image
        (fun r => (r, ⟨(a + i) % n, Nat.mod_lt _ h⟩)))
  else ∅
