import AFTD.Prelude
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.MonomialMul
import AFTD.Kb.Tcs.HammingNormMonomial
import AFTD.Kb.Tcs.HammingNormAddEq

/-!
# hamming_norm_sum_two_degree_six_monomials

Topic: information   Node: 3e77f3e032b2

Provenance: formalization of a published result. Source: arXiv:2610.29807, Lemma 3.2: Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

Let I and J be two 6-element subsets of Fin 12. Then the Hamming norm of the sum of the corresponding coordinate monomials monomial I + monomial J on (Fin 12 → ZMod 2) to ZMod 2 is equal to 128 - 2 ^ ((I ∩ J).card + 1).
-/

/-- Hamming weight of the sum of two degree-6 coordinate monomials in 12 variables. -/
theorem hamming_norm_sum_two_degree_six_monomials
    (I J : Finset (Fin 12)) (hI : I.card = 6) (hJ : J.card = 6) :
    hammingNorm (monomial I + monomial J) = 128 - 2 ^ ((I ∩ J).card + 1) := by
  rw [hamming_norm_add_eq]
  rw [hamming_norm_monomial, hamming_norm_monomial]
  rw [hI, hJ]
  rw [monomial_mul]
  rw [hamming_norm_monomial]
  have h_card : 12 - (I ∪ J).card = (I ∩ J).card := by
    have h_union := Finset.card_union_add_card_inter I J
    omega
  rw [h_card]
  have h_pow : 2 * 2 ^ (I ∩ J).card = 2 ^ ((I ∩ J).card + 1) := by
    ring
  rw [h_pow]
  rfl
