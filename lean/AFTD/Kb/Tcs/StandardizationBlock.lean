import AFTD.Prelude
import AFTD.Kb.Tcs.StandardYoungTableau
import AFTD.Kb.Tcs.StandardYoungTableauBox
import AFTD.Kb.Tcs.StandardYoungTableauDescentSet

/-!
# standardization_block

Topic: combinatorics   Node: 8ec46977ccc6

Provenance: formalization of a published result. Source: arXiv:2611.07715, Theorem 4.3

For a standard Young tableau T on D : Finset (ℕ × ℕ), standardization_block T is the set of fillings M : D → ℕ satisfying M(T.box k) ≤ M(T.box (k+1)) for all 1 ≤ k < D.card, with strict inequality M(T.box k) < M(T.box (k+1)) whenever k belongs to standard_young_tableau_descent_set T.
-/

/-- The standardization block S_T of fillings weakly increasing along T and strictly increasing at descents of T. -/
def standardization_block {D : Finset (ℕ × ℕ)} (T : StandardYoungTableau D) : Set (D → ℕ) := { M : D → ℕ |
  (∀ (k : ℕ) (hk : 1 ≤ k ∧ k < D.card),
    have h1 : k ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨hk.1, le_of_lt hk.2⟩
    have h2 : k + 1 ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
    M (standard_young_tableau_box T k h1) ≤ M (standard_young_tableau_box T (k + 1) h2)) ∧
  (∀ (k : ℕ) (hk : k ∈ standard_young_tableau_descent_set T),
    have h_le : 1 ≤ k ∧ k < D.card := by
      have := Finset.mem_of_mem_filter k hk
      rw [Finset.mem_Ico] at this
      exact this
    have h1 : k ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨h_le.1, le_of_lt h_le.2⟩
    have h2 : k + 1 ∈ Finset.Icc 1 D.card := Finset.mem_Icc.mpr ⟨by omega, h_le.2⟩
    M (standard_young_tableau_box T k h1) < M (standard_young_tableau_box T (k + 1) h2)) }
