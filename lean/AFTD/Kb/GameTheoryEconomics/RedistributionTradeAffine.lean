import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade

/-!
# redistribution_trade_affine

Topic: mechanism_design   Node: ceaee1aa48cc

Provenance: helper lemma. Routine helper in the proof of arXiv:2610.10995, Lemmas4.2/4.3 and equations11/12/20/21. Added while working IN-251. No research advance; the main harmonic bound remains unproved.

The symmetric finite trade average fixes every affine function when the report profile is nonempty.
-/

open Finset MeasureTheory

theorem redistribution_trade_affine {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (a b t : ℝ) :
    redistribution_trade θ (fun x => a*x+b) t = a*t+b := by
  rw [redistribution_trade]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  simp only [mul_add, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp [hn']
  simp only [← Finset.mul_sum, Fintype.card_fin]
  ring
