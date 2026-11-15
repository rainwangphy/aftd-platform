import AFTD.Prelude

/-!
# op223_weighted_shift_arithmetic_certificate

Topic: graphs   Node: 79070cb8479e

Provenance: helper lemma. Exact finite arithmetic for a weighted analogue of Open Problem 6.1, https://arxiv.org/abs/2610.17078.

The displayed rational parameters satisfy two path-resolvent recurrences, two secular equations, and the strict diagonal inequalities used in a proposed fourteen-vertex weighted-shift counterexample. This arithmetic certificate does not itself prove the graph interpretation.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem op223_weighted_shift_arithmetic_certificate :
  let e : ℚ := 8826415565237209674298585338473 / 3517319676169570115263289800000
  let r : ℚ := 3681505299112476434191487709083 / 879329919042392528815822450000
  let z₀ : ℚ := 3
  let z₁ : ℚ := 617/200
  let s : ℚ := 19/100
  let m₀ : ℚ := 4/7
  let m₁ : ℚ := 3970527620571400/7727650084572769
  let c₀ : ℚ := 2/3
  let c₁ : ℚ := (1/4 : ℚ) * (14893022600/12582964721)
  let d₀ : ℚ := z₀/s
  let d₁ : ℚ := z₁/s
  let dv : ℚ := 1/(z₀-c₀) + ((1/2 : ℚ)/(z₀-c₀))^2*d₀
  let dg : ℚ := 8/3 + ((1/2 : ℚ)* (8/3))^2*dv
  let dx : ℚ := 28/3 + ((1/2 : ℚ)*(14/3))^2*dv
  let db : ℚ := 36/5 + ((1/2 : ℚ)*4)^2*dv
  let da : ℚ := 8/15 + ((1/2 : ℚ)*(2/3))^2*dv
  let finalx : ℚ := 45743022600/12582964721 +
        ((1/2 : ℚ) * (22241340000/12582964721))^2*d₁
  let pathdiag := fun k : Fin 6 =>
    let t : ℚ := (k : ℕ)
    2*(t+1)*(6-t)/(z₀*7) + e*d₀*m₀^2*((6-t)/6)^2
  0 < e ∧ 0 < r ∧
  ((fun x : ℚ => 1/(z₀-(9/4 : ℚ)*x))^[5]) (1/z₀) = m₀ ∧
  ((fun x : ℚ => 1/(z₁-(9/4 : ℚ)*x))^[5]) (1/z₁) = m₁ ∧
  z₀ - s/z₀ - r/z₀ - e*m₀ - (1/4 : ℚ)/(z₀-c₀) = 0 ∧
  z₁ - s/z₁ - r/z₁ - e*m₁ - (1/4 : ℚ)/z₁-c₁ = 0 ∧
  dv < d₀ ∧ dg < d₀ ∧ dx < d₀ ∧ db < d₀ ∧ da < d₀ ∧
  1/z₀ + r*d₀/z₀^2 < d₀ ∧
  (∀ k : Fin 6, pathdiag k < d₀) ∧ d₁ < finalx := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num [Function.iterate_succ_apply]
  · norm_num [Function.iterate_succ_apply]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k <;> norm_num
  · norm_num
