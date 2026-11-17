import AFTD.Prelude

/-!
# phase_query_gram_psd_nonneg

Topic: quantum   Node: 528537ed8645

Provenance: helper lemma. Elementary positive-semidefinite matrix inequality for the query Gram SDP, https://arxiv.org/abs/quant-ph/0703141.

Pairing a real positive-semidefinite matrix with a complex Gram matrix has a nonnegative real value.
-/

open scoped BigOperators

/-- Real Gram pairings with positive-semidefinite matrices are nonnegative. -/
theorem phase_query_gram_psd_nonneg {X B : Type} [Fintype X] [Fintype B] (A : Matrix X X ℝ)
    (hA : A.PosSemidef) (v : B → X → ℂ) :
    0 ≤ ∑ b, ∑ x, ∑ y, A x y * ((v b x).re * (v b y).re + (v b x).im * (v b y).im) := by
  apply Finset.sum_nonneg
  intro b hb
  have hr := hA.dotProduct_mulVec_nonneg (fun x => (v b x).re)
  have hi := hA.dotProduct_mulVec_nonneg (fun x => (v b x).im)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hr hi
  have h := add_nonneg hr hi
  simpa only [← Finset.sum_add_distrib, mul_add, mul_comm, mul_left_comm, mul_assoc] using h
