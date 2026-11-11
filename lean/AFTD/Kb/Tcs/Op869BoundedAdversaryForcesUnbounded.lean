import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869AdversaryForces
import AFTD.Kb.Tcs.Op869PredecessorPostdegree
import AFTD.Kb.Tcs.Op869GraphFromPredecessors

/-!
# op869_bounded_adversary_forces_unbounded

Topic: online_algorithms   Node: 3c3e9cb2c7e2

Provenance: helper lemma. arXiv:2610.41516, Section 2.2, post-degree controlled adaptive t-fold coloring simulation.

A winning post-degree-bounded t-fold adversary position also wins the same game without the post-degree restriction.
-/

theorem op869_bounded_adversary_forces_unbounded {n : ℕ} (k t K D fuel i : ℕ)
    (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (h : op869_bounded_adversary_forces k t K D fuel i P C) :
    op869_adversary_forces k t K fuel i P C := by
  induction fuel generalizing i P C with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    by_cases hi : i < n
    · simp only [op869_bounded_adversary_forces, dif_pos hi] at h
      simp only [op869_adversary_forces, dif_pos hi]
      obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
      refine ⟨S, hS, hcolor, ?_⟩
      intro c hc hvalid
      rcases hnext c hc hvalid with hwin | hgame
      · exact Or.inl hwin
      · exact Or.inr (ih (i + 1) _ _ hgame)
    · simp [op869_bounded_adversary_forces, hi] at h
