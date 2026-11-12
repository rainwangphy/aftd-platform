import AFTD.Prelude

/-!
# op_193_stable_anchor_avoidance_forces_nonanchor

Topic: graphs   Node: e5f226966f92

Provenance: helper lemma. Stable-anchor refinement of the coloring argument in arXiv:2610.17884 Section 3.

If every family of q stable k-sets can be met in at most one point by a stable k-set, every q-coloring has a nonanchored color class.
-/

theorem op_193_stable_anchor_avoidance_forces_nonanchor (m k q : ℕ)
    (c : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin q)
    (havoid : ∀ A : Fin q → {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
      ∃ S : {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
        ∀ j, (S.1 ∩ (A j).1).card ≤ 1) :
    ∃ j : Fin q, ∀ U, c U = j → ∃ W, c W = j ∧ (U.1 ∩ W.1).card < 2 := by
  classical
  by_contra hn
  push_neg at hn
  choose A hcolor hanchor using hn
  obtain ⟨S, hS⟩ := havoid A
  have hlarge := hanchor (c S) S rfl
  have hsmall := hS (c S)
  rw [Finset.inter_comm] at hlarge
  omega
