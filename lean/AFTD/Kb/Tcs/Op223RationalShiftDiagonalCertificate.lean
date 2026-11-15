import AFTD.Prelude

/-!
# op223_rational_shift_diagonal_certificate

Topic: graphs   Node: 2e567b8f8e35

Provenance: helper lemma. Exact finite arithmetic for the rational weighted-shift example, experiment 27866.

The displayed rational values satisfy the root secular identity and the strict core, tail, and six path diagonal inequalities for the proposed rational weighted example. Its matrix interpretation needs separate proof.
-/

set_option maxHeartbeats 1000000

theorem op223_rational_shift_diagonal_certificate :
  let C : ℚ := 272781/137530
  let P : ℚ := 5913/13753
  let E : ℚ := 6597/4045
  let d : ℚ := 3/P^2
  let dv : ℚ := 3/7 + ((3/14 : ℚ)^2)*d
  let dj : ℚ := 8/3 + ((4/3 : ℚ)^2)*dv
  let dx : ℚ := 28/3 + ((7/3 : ℚ)^2)*dv
  let db : ℚ := 36/5 + (2 : ℚ)^2*dv
  let da : ℚ := 8/15 + ((1/3 : ℚ)^2)*dv
  let tail : ℚ := 1/3 + C^2*d/9
  let pathdiag := fun k : Fin 6 =>
    let t : ℚ := (k : ℕ)
    2*(t+1)*(6-t)/21 + E^2*d*(4/7 : ℚ)^2*((6-t)/6)^2
  C^2+P^2+(12/7 : ℚ)*E^2 = 243/28 ∧
  dv < d ∧ dj < d ∧ dx < d ∧ db < d ∧ da < d ∧ tail < d ∧
  (∀ k : Fin 6, pathdiag k < d) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro k
    fin_cases k <;> norm_num
