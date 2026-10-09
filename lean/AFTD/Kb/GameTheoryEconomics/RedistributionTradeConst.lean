import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade

/-!
# redistribution_trade_const

Topic: mechanism_design   Node: b0bd70d35adb

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision): the operations average, so they fix constants.

The trade operation maps a constant function to itself.
-/

theorem redistribution_trade_const {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (c t : ℝ) :
    redistribution_trade θ (fun _ => c) t = c := by
  unfold redistribution_trade
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
