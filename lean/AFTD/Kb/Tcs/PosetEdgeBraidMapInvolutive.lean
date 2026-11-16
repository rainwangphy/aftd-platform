import AFTD.Prelude
import AFTD.Kb.Tcs.PosetEdgeBraidMap

/-!
# poset_edge_braid_map_involutive

Topic: combinatorics   Node: d23189db2d66

Provenance: helper lemma. arXiv:2611.15540, Section 3

For any partially ordered set P with decidable equality, the map poset_edge_braid_map is an involution on pairs: poset_edge_braid_map (poset_edge_braid_map p) = p.
-/

/-- The poset bipartite braid map E_P is an involution. -/
theorem poset_edge_braid_map_involutive {P : Type*} [PartialOrder P] [DecidableEq P]
    (p : ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2)) × ({p : P × P // p.1 ≤ p.2} ⊕ (P × ZMod 2))) :
    poset_edge_braid_map (poset_edge_braid_map p) = p := by
  have ht (l : {p : P × P // p.1 ≤ p.2}) (z : P × ZMod 2) :
      (if (if z = (l.val.1, 0) then (l.val.2, 1) else if z = (l.val.2, 1) then (l.val.1, 0) else z) = (l.val.1, 0)
       then (l.val.2, 1)
       else if (if z = (l.val.1, 0) then (l.val.2, 1) else if z = (l.val.2, 1) then (l.val.1, 0) else z) = (l.val.2, 1)
       then (l.val.1, 0)
       else if z = (l.val.1, 0) then (l.val.2, 1) else if z = (l.val.2, 1) then (l.val.1, 0) else z) = z := by
    have hne : (l.val.2, (1 : ZMod 2)) ≠ (l.val.1, (0 : ZMod 2)) := by
      intro h
      have : (1 : ZMod 2) = 0 := Prod.ext_iff.mp h |>.2
      revert this; decide
    by_cases h1 : z = (l.val.1, 0)
    · subst h1; simp [hne]
    · by_cases h2 : z = (l.val.2, 1)
      · subst h2; simp
      · simp [h1, h2]
  rcases p with ⟨l1 | z1, l2 | z2⟩
  · rfl
  · dsimp [poset_edge_braid_map]
    rw [ht]
  · dsimp [poset_edge_braid_map]
    rw [ht]
  · rfl
