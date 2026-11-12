import AFTD.Prelude

/-!
# op_193_avoidance_forces_nonanchor

Topic: graphs   Node: f69b84e25804

Provenance: helper lemma. Anchor-avoidance reduction for OP-193.

If every family of q sets of at most k cycle vertices admits a stable k-set meeting each set in at most one point, every q-coloring of the stable k-sets has a nonanchored color class.
-/

theorem op_193_avoidance_forces_nonanchor (m k q : ℕ)
    (c : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin q)
    (havoid : ∀ A : Fin q → Finset (Fin m), (∀ j, (A j).card ≤ k) →
      ∃ S : {S : Finset (Fin m) // S.card = k ∧
        (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))},
        ∀ j, (S.1 ∩ A j).card ≤ 1) :
    ∃ j : Fin q, ∀ U, c U = j → ∃ W, c W = j ∧ (U.1 ∩ W.1).card < 2 := by
  classical
  by_contra hn
  push_neg at hn
  choose A hcolor hanchor using hn
  obtain ⟨S, hS⟩ := havoid (fun j => (A j).1) (by intro j; rw [(A j).2.1])
  have hlarge := hanchor (c S) S rfl
  have hsmall := hS (c S)
  rw [Finset.inter_comm] at hlarge
  omega
