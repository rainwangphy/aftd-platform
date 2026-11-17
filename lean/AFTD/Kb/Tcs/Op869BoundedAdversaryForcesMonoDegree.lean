import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_adversary_forces_mono_degree

Topic: online_algorithms   Node: 5ce08bae05c9

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

Increasing the post-degree bound preserves a winning position in the bounded t-fold adversary game.
-/

/-- Raising the post-degree budget of the bounded adversary game keeps every winning position winning. -/
theorem op869_bounded_adversary_forces_mono_degree {n : ℕ} (k t K : ℕ) (D D' : ℕ) (hDD : D ≤ D')
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k t K D' fuel i P C := by
  induction fuel generalizing i P C with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_bounded_adversary_forces, dif_pos hi] at h ⊢
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
      refine ⟨S, hS, hcolor, fun a => le_trans (hdegree a) hDD, ?_⟩
      intro c hc hvalid
      rcases hnext c hc hvalid with hw | hrec
      · exact Or.inl hw
      · exact Or.inr (ih (i + 1) _ _ hrec)
    · simp [op869_bounded_adversary_forces, hi] at h
