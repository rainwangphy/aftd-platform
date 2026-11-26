import AFTD.Prelude
import AFTD.Kb.Tcs.QutritConvolutionChoi

/-!
# qutrit_zero_face_chart_square

Topic: quantum   Node: 74481130cd1d

Provenance: helper lemma. OP-2299 zero-Bell face local jet, exact experiment 40952.

At the coordinate zero-face chart, the exceptional rank-one witness evaluates to an explicit Hermitian square.
-/

theorem qutrit_zero_face_chart_square (a b c : ℂ) :
    let x : Fin 3 → ℂ := ![1, a, b]
    let y : Fin 3 → ℂ := ![-star a - star b * c, 1, c]
    let H : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
    let Q := b + star c - a^2 - a*b*star c
    3 * (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
      star (x p.1 * y p.2) * qutrit_convolution_choi H p q * (x q.1 * y q.2)) = star Q * Q := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, qutrit_convolution_choi]
  <;> ring
