import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370ParameterRankOneSensitivity
import AFTD.Kb.Tcs.Op1370NeighborSignedNonleafNonzero

/-!
# op1370_lower_rank_sensitivity

Topic: combinatorics   Node: 178cde65a8d7

Provenance: helper lemma.

A lower-rank nonleaf has a nonzero rank-one response when the response equations have a solution.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_lower_rank_sensitivity
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (J : Matrix ι ι ℚ) (f : ℚ[X] →+* K) (hf : Function.Injective f)
    (N : Finset ι) (x : ι) (hx : x ∉ N) (hcard : N.card ≠ 1)
    (L R σ : ι → ℚ) (hσ : σ x ≠ 0)
    (hs : ∀ a ∈ N, σ a = -σ x)
    (hL : ∀ a, L a = if a = x then 1 else 0)
    (hR : ∀ a, R a = if a = x then 1 else if a ∈ N then 1 else 0)
    (z : ι → K) (t : K) (ht : t ≠ 0)
    (hz : let A := ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
      A.mulVec z + (t * ((fun a => f (Polynomial.C (R a))) ⬝ᵥ z)) •
        (A.det • (fun a => f (Polynomial.C (L a)))) =
        A.det • (fun a => f (Polynomial.C (σ a)))) :
    let A := ((Polynomial.X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) + J.map Polynomial.C).map f
    (fun _ : ι => f (Polynomial.C 1)) ⬝ᵥ z ≠
      (fun _ : ι => f (Polynomial.C 1)) ⬝ᵥ
        (A.adjugate.mulVec (fun a => f (Polynomial.C (σ a)))) := by
  classical
  have hsum : (∑ a, (1 : ℚ) * L a) = 1 := by
    rw [Finset.sum_eq_single x]
    · simp [hL]
    · intro a _ ha
      simp [hL, ha]
    · intro h
      exact (h (Finset.mem_univ x)).elim
  have hwl : (∑ a, (1 : ℚ) * L a) ≠ 0 := by rw [hsum]; exact one_ne_zero
  have hrb : (∑ a, R a * σ a) ≠ 0 := by
    simpa only [hR, ite_mul, one_mul, zero_mul] using
      op1370_neighbor_signed_nonleaf_nonzero N x hx hcard σ hσ hs
  exact op1370_parameter_rank_one_sensitivity J f hf L R (fun _ => 1) σ z t ht hwl hrb hz
