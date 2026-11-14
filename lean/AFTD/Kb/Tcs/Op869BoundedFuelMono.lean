import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_fuel_mono

Topic: online_algorithms   Node: 9e55273e0a84

Provenance: helper lemma. A monotonicity step in the finite online coloring game for arXiv:2610.41516, Section 2.

Increasing the number of remaining moves preserves a winning position in the bounded online coloring adversary game.
-/

theorem op869_bounded_fuel_mono {n : ℕ} (k t K D : ℕ) (fuel fuel' i : ℕ) (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ) (hle : fuel ≤ fuel') (h : op869_bounded_adversary_forces k t K D fuel i P C) : op869_bounded_adversary_forces k t K D fuel' i P C := by
  induction fuel generalizing fuel' i P C with
  | zero => simp [op869_bounded_adversary_forces] at h
  | succ fuel ih =>
    cases fuel' with
    | zero => omega
    | succ fuel' =>
      by_cases hi : i < n
      · simp only [op869_bounded_adversary_forces, dif_pos hi] at h ⊢
        obtain ⟨S, hS, hcolor, hdegree, hnext⟩ := h
        refine ⟨S, hS, hcolor, hdegree, ?_⟩
        intro c hc hvalid
        rcases hnext c hc hvalid with hw | hrec
        · exact Or.inl hw
        · exact Or.inr (ih fuel' (i+1) _ _ (by omega) hrec)
      · simp [op869_bounded_adversary_forces, hi] at h
