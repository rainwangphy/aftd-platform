import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_adversary_forces_mono_k

Topic: online_algorithms   Node: a75c50bb81fd

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

Allowing more colours for the colour player preserves a winning position in the bounded adversary game.
-/

/-- A winning position in the bounded game with k colours allowed stays winning when k is enlarged. -/
theorem op869_bounded_adversary_forces_mono_k {n : ℕ} (k k' t K D : ℕ) (hkk : k ≤ k')
    (fuel i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k' t K D fuel i P C := by
  induction fuel generalizing i P C with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_bounded_adversary_forces, dif_pos hi] at h ⊢
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
      refine ⟨S, hS, hcolor.mono hkk, hdegree, ?_⟩
      intro c hc hvalid
      rcases hnext c hc hvalid with hw | hrec
      · exact Or.inl hw
      · exact Or.inr (ih (i + 1) _ _ hrec)
    · simp [op869_bounded_adversary_forces, hi] at h
