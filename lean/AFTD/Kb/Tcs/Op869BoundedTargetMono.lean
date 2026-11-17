import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_target_mono

Topic: online_algorithms   Node: 33cf0a600ec3

Provenance: helper lemma. Monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Reducing the target number of colors preserves any winning position in the bounded adversary game.
-/

/-- Reducing the target number of colors preserves any winning position in the bounded adversary game. -/
theorem op869_bounded_target_mono {n : ℕ} (k t K K' D : ℕ) (hKK : K' ≤ K) (fuel i : ℕ)
    (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k t K' D fuel i P C := by
  induction fuel generalizing i P C with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_bounded_adversary_forces, dif_pos hi] at h ⊢
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
      refine ⟨S, hS, hcolor, hdegree, ?_⟩
      intro c hc hvalid
      rcases hnext c hc hvalid with hw | hrec
      · exact Or.inl (le_trans hKK hw)
      · exact Or.inr (ih (i + 1) _ _ hrec)
    · simp [op869_bounded_adversary_forces, hi] at h
