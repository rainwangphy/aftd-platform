import AFTD.Prelude
import AFTD.Kb.Tcs.Op861FourierCubeIdentity
import AFTD.Kb.Tcs.Op861FourierPairIdentity
import AFTD.Kb.Tcs.Op861OrderThreeCharacterSumBound
import AFTD.Kb.Tcs.Op861OrderThreeZeroSumUpper
import AFTD.Kb.Tcs.Op861CrossingEstimateArithmetic
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op861_ternary_crossing_pairs_dense

Topic: graphs   Node: 90a66e1c581a

Provenance: helper lemma. A ternary affine triangle crossing estimate for the probabilistic tournament construction of OP-861.

For every positive d and every subset S of the d-dimensional ternary vector space with twice its size equal to 3^d+1, there are at least 3^(2d)/24 ordered pairs of points x,y in S whose third point −x−y lies outside S.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000

theorem op861_ternary_crossing_pairs_dense (d : ℕ) (hd : 0 < d)
    (S : Finset (Fin d → ZMod 3)) (hS : 2 * S.card = 3^d + 1) :
    (3^d)^2 ≤ 24 * ((S.product S).filter (fun xy => -(xy.1 + xy.2) ∉ S)).card := by
  classical
  let G := (Fin d → ZMod 3)
  have hcard : Fintype.card G = 3^d := by simp [G]
  have hthree : 3 ≤ 3^d := by
    cases d with
    | zero => omega
    | succ e =>
      have hp : 0 < (3:ℕ)^e := by positivity
      rw [pow_succ]
      nlinarith
  have h3 (t : G) : t+t+t = 0 := by
    funext i
    change t i + t i + t i = 0
    calc
      _ = (3 : ZMod 3) * t i := by ring
      _ = 0 := by
        have h : (3 : ZMod 3) = 0 := by decide
        rw [h, zero_mul]
  let T : ℕ := ((S.product S).filter (fun xy => -(xy.1+xy.2) ∈ S)).card
  let P : ℕ := ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card
  have hcountN : T + P = S.card^2 := by
    dsimp [T,P]
    simpa [Finset.card_product, pow_two] using
      (Finset.card_filter_add_card_filter_not (s := S.product S)
        (fun xy => -(xy.1+xy.2) ∈ S))
  have hcountR : (T:ℝ) + P = (S.card:ℝ)^2 := by exact_mod_cast hcountN
  have hk : 2 * (S.card:ℝ) = (Fintype.card G:ℝ) + 1 := by
    rw [hcard]
    exact_mod_cast hS
  have hn : 3 ≤ (Fintype.card G : ℝ) := by rw [hcard]; exact_mod_cast hthree
  have hfourier : 3 * (Fintype.card G : ℝ) * (T:ℝ) ≤
      3 * (S.card:ℝ)^3 + (Fintype.card G:ℝ) *
        ((Fintype.card G:ℝ)*(S.card:ℝ) - (S.card:ℝ)^2) := by
    simpa [T, G] using op861_order_three_zero_sum_upper G h3 S
  have hf := op861_crossing_estimate_arithmetic (Fintype.card G : ℝ)
    (S.card:ℝ) (P:ℝ) (T:ℝ) hn hk hcountR hfourier
  rw [hcard] at hf
  dsimp [P] at hf
  exact_mod_cast hf
