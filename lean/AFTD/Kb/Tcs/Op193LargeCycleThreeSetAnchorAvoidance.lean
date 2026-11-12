import AFTD.Prelude
import AFTD.Kb.Tcs.Op193CubicCycleAnchorAvoidance

/-!
# op_193_large_cycle_three_set_anchor_avoidance

Topic: graphs   Node: 705352222b8a

Provenance: helper lemma. Triangle-free extremal reduction for the anchored-color argument in arXiv:2610.17884 Section 3.

For every cycle of length at least 15, any m-4 sets of at most three cycle vertices are simultaneously met in at most one vertex by some stable triple.
-/

theorem op_193_large_cycle_three_set_anchor_avoidance (m : ℕ) (hm : 15 ≤ m)
    (A : Fin (m-4) → Finset (Fin m))
    (hA : ∀ j, (A j).card ≤ 3) :
    ∃ S : Finset (Fin m), S.card = 3 ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m)) ∧
      ∀ j, (S ∩ A j).card ≤ 1 := by
  have hk : 3 ≤ 3 := le_refl 3
  have hm' : 3 * ((3 - 1) ^ 2 + 1) ≤ m := by omega
  have h_eq : m - 2 * 3 + 2 = m - 4 := by omega
  have hA' : ∀ j : Fin (m - 2 * 3 + 2), (A (Fin.cast h_eq j)).card ≤ 3 := fun j => hA (Fin.cast h_eq j)
  obtain ⟨S, hScard, hSindep, hSinter⟩ :=
    op_193_cubic_cycle_anchor_avoidance 3 m hk hm' (fun j => A (Fin.cast h_eq j)) hA'
  refine ⟨S, hScard, hSindep, ?_⟩
  intro j
  have hj : j = Fin.cast h_eq (Fin.cast h_eq.symm j) := by simp
  rw [hj]
  exact hSinter (Fin.cast h_eq.symm j)
