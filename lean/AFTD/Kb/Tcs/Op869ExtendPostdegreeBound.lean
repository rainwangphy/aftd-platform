import AFTD.Prelude
import AFTD.Kb.Tcs.Op869PredecessorPostdegree
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869MemExtendPredecessors
import AFTD.Kb.Tcs.Op869ExtendPostdegree

/-!
# op869_extend_postdegree_bound

Topic: online_algorithms   Node: 787e08553ce4

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

If every original post-degree is at most D, padding preserves this bound at all vertices.
-/

/-- If every original post-degree is at most D, padding preserves this bound at all vertices. -/
theorem op869_extend_postdegree_bound {n m : ℕ} (h : n ≤ m)
    (P : Fin n → Finset (Fin n)) (D : ℕ)
    (hD : ∀ a, op869_predecessor_postdegree P a ≤ D) :
    ∀ x, op869_predecessor_postdegree (op869_extend_predecessors h P) x ≤ D := by
  classical
  intro x
  by_cases hx : x.val < n
  · let a : Fin n := ⟨x.val, hx⟩
    have hax : Fin.castLE h a = x := by ext; rfl
    rw [← hax, op869_extend_postdegree]
    exact hD a
  · have hz : op869_predecessor_postdegree (op869_extend_predecessors h P) x = 0 := by
      unfold op869_predecessor_postdegree
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro y hy hmem
      obtain ⟨a,b,ha,hb,hab⟩ := (op869_mem_extend_predecessors h P x y).mp hmem.2
      have hx' : x.val < n := by
        rw [← ha]
        exact a.isLt
      exact hx hx'
    simp [hz]
