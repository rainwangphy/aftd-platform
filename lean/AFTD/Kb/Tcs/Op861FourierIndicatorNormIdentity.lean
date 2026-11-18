import AFTD.Prelude
import AFTD.Kb.Tcs.Op861FourierPairIdentity

/-!
# op861_fourier_indicator_norm_identity

Topic: graphs   Node: 901f44fcedc9

Provenance: helper lemma. Finite Fourier orthogonality, used for op861_ternary_crossing_pairs_dense.

For a finite abelian group and a finite subset, the sum over additive characters of the squared norm of the character sum over the subset equals the group order times the size of the subset.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000

theorem op861_fourier_indicator_norm_identity (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (S : Finset G) :
    (∑ χ : AddChar G ℂ, ‖∑ x ∈ S, χ x‖^2) =
      (Fintype.card G : ℝ) * S.card := by
  classical
  let f : G → ℂ := fun x => if x ∈ S then 1 else 0
  have hF (χ : AddChar G ℂ) : (∑ x : G, f x * χ x) = ∑ x ∈ S, χ x := by
    simp [f]
  have hG (χ : AddChar G ℂ) : (∑ x : G, f x * χ (-x)) = star (∑ x ∈ S, χ x) := by
    simp [f, AddChar.map_neg_eq_conj]
  have hsquared (χ : AddChar G ℂ) :
      ((‖∑ x ∈ S, χ x‖^2 : ℝ) : ℂ) =
        (∑ x : G, f x * χ x) * (∑ x : G, f x * χ (-x)) := by
    rw [hF, hG]
    simpa [Complex.star_def, Complex.normSq_eq_norm_sq, mul_comm] using
      (Complex.normSq_eq_conj_mul_self (z := ∑ x ∈ S, χ x))
  have hdiag : (∑ x : G, f x * f x) = (S.card : ℂ) := by
    simp [f]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [hsquared]
  rw [op861_fourier_pair_identity G f f, hdiag]
