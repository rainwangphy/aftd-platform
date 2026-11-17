import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_adversary_forces_mono_colors

Topic: online_algorithms   Node: 79065fd2b491

Provenance: helper lemma. step towards op869_online_coloring_deterministic_lower_bound

Enlarging the recorded colour set of every vertex pointwise preserves a winning position in the bounded adversary game.
-/

/-- A larger recorded colour set only restricts the moves available to the colour player, so it is still winning. -/
theorem op869_bounded_adversary_forces_mono_colors {n : ℕ} (k t K D : ℕ) (fuel i : ℕ)
    (P : Fin n → Finset (Fin n)) (C C' : Fin n → Finset ℕ) (hsub : ∀ a, C a ⊆ C' a)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_bounded_adversary_forces k t K D fuel i P C' := by
  classical
  induction fuel generalizing i P C C' with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_bounded_adversary_forces, dif_pos hi] at h ⊢
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
      refine ⟨S, hS, hcolor, hdegree, ?_⟩
      intro c hc hvalid
      have hv : ∀ a ∈ S, Disjoint (C a) c := by
        intro a ha
        exact (hvalid a ha).mono_left (hsub a)
      have hsub' : ∀ a, Function.update C (⟨i,hi⟩ : Fin n) c a ⊆
          Function.update C' (⟨i,hi⟩ : Fin n) c a := by
        intro a
        by_cases ha : a = (⟨i,hi⟩ : Fin n)
        · subst a; simp
        · simpa [Function.update_of_ne ha] using hsub a
      rcases hnext c hc hv with hw | hrec
      · left
        apply le_trans hw
        apply Finset.card_le_card
        apply Finset.biUnion_mono
        intro a ha
        exact hsub' a
      · right
        exact ih (i+1) _ _ _ hsub' hrec
    · simp [op869_bounded_adversary_forces, hi] at h
