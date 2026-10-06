import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcpIsBestResponse

/-!
# pcp_half_two_best_response

Topic: equilibria   Node: 2cd4807a89f0

Provenance: formalization of a published result. Source: The Publication Choice Problem, AAAI 2026 (arXiv:2511.13678v2), Lemma 3.1 (closed-form best response to Program (1)); special case alpha = 1/2, beta = 2

For alpha = 1/2 and beta = 2 with positive costs, the closed form of Lemma 3.1, a_j = v_j^4 / (c_j^2 sum_l v_l^4/c_l), solves the researcher's Program (1) (Cauchy-Schwarz / AM-GM).
-/

open Finset in
/-- For `α = 1/2`, `β = 2` and positive costs, the closed form of Lemma 3.1 of arXiv:2511.13678, `a j = v j ^ 4 / (c j ^ 2 * D)` with `D = ∑ j, v j ^ 4 / c j > 0`, is a best response. -/
lemma pcp_half_two_best_response {k : ℕ} (c v : Fin k → ℝ) (hc : ∀ j, 0 < c j)
    (hD : 0 < ∑ j, v j ^ 4 / c j) :
    pcp_is_best_response (1 / 2) 2 c v (fun j => v j ^ 4 / (c j ^ 2 * ∑ l, v l ^ 4 / c l)) := by
  set D := ∑ l, v l ^ 4 / c l with hDdef
  set s := Real.sqrt D with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hD
  have hss : s ^ 2 = D := Real.sq_sqrt hD.le
  have hrp : ∀ x : ℝ, 0 ≤ x → x ^ (1 / 2 : ℝ) = Real.sqrt x := fun x _ => (Real.sqrt_eq_rpow x).symm
  have hv2 : ∀ j, v j ^ (2 : ℝ) = v j ^ 2 := fun j => Real.rpow_two (v j)
  have ha_nn : ∀ j, 0 ≤ v j ^ 4 / (c j ^ 2 * D) := fun j => by
    have := hc j; positivity
  have hsqrt_a : ∀ j, Real.sqrt (v j ^ 4 / (c j ^ 2 * D)) = v j ^ 2 / (c j * s) := fun j => by
    have hcj := hc j
    have : v j ^ 4 / (c j ^ 2 * D) = (v j ^ 2 / (c j * s)) ^ 2 := by
      rw [div_pow, mul_pow, hss]; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hval : ∑ j, (v j ^ 4 / (c j ^ 2 * D)) ^ (1 / 2 : ℝ) * v j ^ (2 : ℝ) = s := by
    have : ∀ j, (v j ^ 4 / (c j ^ 2 * D)) ^ (1 / 2 : ℝ) * v j ^ (2 : ℝ) = (v j ^ 4 / c j) / s := by
      intro j
      have hcj := hc j
      rw [hrp _ (ha_nn j), hsqrt_a, hv2]
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_div, ← hDdef, ← hss]
    field_simp
  refine ⟨ha_nn, ?_, ?_⟩
  · have : ∀ j, v j ^ 4 / (c j ^ 2 * D) * c j = (v j ^ 4 / c j) / D := by
      intro j
      have hcj := hc j
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_div, ← hDdef, div_self hD.ne']
  · intro a' ha' hbud
    rw [hval]
    have hterm : ∀ j, a' j ^ (1 / 2 : ℝ) * v j ^ (2 : ℝ) ≤
        s * (a' j * c j) / 2 + (v j ^ 4 / c j) / (2 * s) := by
      intro j
      have hcj := hc j
      rw [hrp _ (ha' j), hv2]
      set r := Real.sqrt (a' j) with hr
      have hr2 : r ^ 2 = a' j := Real.sq_sqrt (ha' j)
      rw [← hr2]
      have key : s * (r ^ 2 * c j) / 2 + v j ^ 4 / c j / (2 * s) - r * v j ^ 2 =
          (s * c j * r - v j ^ 2) ^ 2 / (2 * s * c j) := by
        field_simp; ring
      have : 0 ≤ (s * c j * r - v j ^ 2) ^ 2 / (2 * s * c j) := by positivity
      linarith
    calc ∑ j, a' j ^ (1 / 2 : ℝ) * v j ^ (2 : ℝ)
        ≤ ∑ j, (s * (a' j * c j) / 2 + (v j ^ 4 / c j) / (2 * s)) := Finset.sum_le_sum fun j _ => hterm j
      _ = s * (∑ j, a' j * c j) / 2 + D / (2 * s) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum, hDdef]
      _ ≤ s * 1 / 2 + D / (2 * s) := by gcongr
      _ = s := by rw [← hss]; field_simp; ring
