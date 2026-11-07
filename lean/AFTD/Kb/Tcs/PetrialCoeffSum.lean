import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# petrial_coeff_sum

Topic: combinatorics   Node: e9e38ac06e57

Provenance: helper lemma. arXiv:2611.07503, Section 3

For any simple graph G on a finite type V with decidable equality and decidable adjacency, the sum of petrial_coeff G k for k in the range from 0 to Fintype.card V + 1 equals 2 ^ (Fintype.card V).
-/

/-- The sum of the partial Petrial coefficients equals 2^|V|. -/
theorem petrial_coeff_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ k ∈ Finset.range (Fintype.card V + 1), petrial_coeff G k = 2 ^ Fintype.card V := by
  have hmaps : Set.MapsTo (fun F : Finset V => (petrial_matrix G F).rank)
      (↑(Finset.univ : Finset (Finset V))) (↑(Finset.range (Fintype.card V + 1))) := by
    intro F _
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (petrial_matrix G F).rank_le_card_width
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_finset] at hfiber
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro k _
  rfl
