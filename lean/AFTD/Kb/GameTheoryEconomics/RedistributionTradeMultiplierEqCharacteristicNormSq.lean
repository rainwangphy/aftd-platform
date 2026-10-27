import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeMultiplier
import AFTD.Kb.GameTheoryEconomics.RedistributionCharacteristic

/-!
# redistribution_trade_multiplier_eq_characteristic_normSq

Topic: mechanism_design   Node: daf766199a9f

Provenance: helper lemma. Routine finite-characteristic-function helper for IN-251, arXiv:2610.10995 Lemma4.3 Steps1/2 and equation12. These statements do not assert the half-plane boundary integral inequality or the main harmonic error bound. No research advance.

At a real frequency, the squared empirical cosine/sine multiplier equals the squared complex norm of the characteristic function.
-/

open Finset MeasureTheory

theorem redistribution_trade_multiplier_eq_characteristic_normSq {n : ℕ}
    (θ : Fin n → ℝ) (u : ℝ) :
    redistribution_trade_multiplier θ u =
      Complex.normSq (redistribution_characteristic θ (u : ℂ)) := by
  unfold redistribution_trade_multiplier redistribution_characteristic
  have hterm : ∀ j, Complex.exp (Complex.I * (u:ℂ) * ↑(θ j))
      = ↑(Real.cos (u * θ j)) + ↑(Real.sin (u * θ j)) * Complex.I := by
    intro j
    have h : Complex.I * (u:ℂ) * ↑(θ j) = ↑(u * θ j) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_ofReal_mul_I]
  have hsum : (∑ j, Complex.exp (Complex.I * (u:ℂ) * ↑(θ j)))
      = ↑(∑ j, Real.cos (u * θ j)) + ↑(∑ j, Real.sin (u * θ j)) * Complex.I := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Complex.ofReal_sum, ← Complex.ofReal_sum]
  rw [hsum]
  have h1 : (1 / (n:ℂ)) = ↑((1:ℝ)/(n:ℝ)) := by rw [Complex.ofReal_div]; norm_num
  rw [h1, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_add_mul_I]
  simp only [one_div]
  ring
