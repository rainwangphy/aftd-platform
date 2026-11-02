import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Coloring
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field

/-!
# maxcut_cycle71_force_closed_core

Topic: equilibria   Node: 3facfa2a90c1

Provenance: helper lemma. The forced-neighbor dependency graph in the 71-vertex minimal-deviation construction; experiment 12450.

Any nonempty set of core vertices closed under adjacent vertices whose initial color is the first vertex’s deviation color contains all 32 core vertices.
-/

/-- A closed walk through the forcing relation that visits all 32 core vertices. -/
def mc71_walk (i : ℕ) : Fin 71 :=
  [8, 1, 17, 9, 2, 18, 10, 0, 16, 13, 3, 19, 11, 4, 20, 12, 5, 21, 10, 6, 22, 14, 7, 23,
    15, 25, 10, 24, 11, 26, 8, 27, 8, 28, 8, 29, 8, 30, 8, 31].getD (i % 40) 0

theorem mc71_walk_step :
    ∀ i : Fin 40, (mc71_walk i.val).val < 32 ∧ (mc71_walk (i.val + 1)).val < 32 ∧
      maxcut_cycle71_graph.Adj (mc71_walk i.val) (mc71_walk (i.val + 1)) ∧
      maxcut_cycle71_coloring 0 (mc71_walk (i.val + 1)) = maxcut_cycle71_coloring 1 (mc71_walk i.val) := by
  unfold maxcut_cycle71_graph maxcut_cycle71_field
  simp only [SimpleGraph.fromRel_adj]
  decide +kernel

theorem mc71_walk_covers : ∀ w : Fin 71, w.val < 32 → ∃ j : Fin 40, mc71_walk j.val = w := by
  decide +kernel

theorem mc71_walk_mod (i : ℕ) : mc71_walk (i % 40) = mc71_walk i := by
  unfold mc71_walk; rw [Nat.mod_mod]

theorem maxcut_cycle71_force_closed_core (S : Finset (Fin 71))
    (hne : S.Nonempty) (hcore : ∀ v ∈ S, v.val < 32)
    (hclosed : ∀ v ∈ S, ∀ w : Fin 71, w.val < 32 →
      maxcut_cycle71_graph.Adj v w → maxcut_cycle71_coloring 0 w = maxcut_cycle71_coloring 1 v → w ∈ S) :
    ∀ w : Fin 71, w.val < 32 → w ∈ S := by
  have hstep : ∀ i : ℕ, mc71_walk i ∈ S → mc71_walk (i + 1) ∈ S := by
    intro i hi
    have h := mc71_walk_step ⟨i % 40, Nat.mod_lt _ (by norm_num)⟩
    simp only at h
    have e1 : mc71_walk (i % 40) = mc71_walk i := mc71_walk_mod i
    have e2 : mc71_walk (i % 40 + 1) = mc71_walk (i + 1) := by
      rw [← mc71_walk_mod (i % 40 + 1), ← mc71_walk_mod (i + 1), Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod]
    rw [e1, e2] at h
    exact hclosed _ hi _ h.2.1 h.2.2.1 h.2.2.2
  have hiter : ∀ i k : ℕ, mc71_walk i ∈ S → mc71_walk (i + k) ∈ S := by
    intro i k hi
    induction k with
    | zero => simpa using hi
    | succ k ih => exact hstep _ ih
  obtain ⟨v, hv⟩ := hne
  obtain ⟨i, hi⟩ := mc71_walk_covers v (hcore v hv)
  intro w hw
  obtain ⟨j, hj⟩ := mc71_walk_covers w hw
  have h := hiter i.val (j.val + 40 - i.val) (hi ▸ hv)
  have e : i.val + (j.val + 40 - i.val) = j.val + 40 := by omega
  rw [e, ← mc71_walk_mod, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt, hj] at h
  exact h
