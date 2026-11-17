import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ExtendPredecessors

/-!
# op869_mem_extend_predecessors

Topic: online_algorithms   Node: c9a320eba86a

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Membership in a padded predecessor set is equivalent to original membership under the initial-segment embedding.
-/

/-- Membership in a padded predecessor set is equivalent to original membership under the initial-segment embedding. -/
theorem op869_mem_extend_predecessors {n m : ℕ} (h : n ≤ m) (P : Fin n → Finset (Fin n)) (x y : Fin m) :
    x ∈ op869_extend_predecessors h P y ↔
    ∃ a b : Fin n, Fin.castLE h a = x ∧ Fin.castLE h b = y ∧ a ∈ P b := by
  classical
  unfold op869_extend_predecessors
  split_ifs with hy
  · simp only [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩
      exact ⟨a, ⟨y.val, hy⟩, hax, by ext; rfl, ha⟩
    · rintro ⟨a, b, hax, hby, hab⟩
      have hb : b = ⟨y.val, hy⟩ := by
        apply Fin.ext
        exact congrArg (fun z : Fin m => z.val) hby
      subst b
      exact ⟨a, hab, hax⟩
  · simp only [Finset.notMem_empty, false_iff]
    rintro ⟨a, b, hax, hby, hab⟩
    have : y.val < n := by
      rw [← hby]
      exact b.isLt
    exact hy this
