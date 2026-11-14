import AFTD.Prelude

/-!
# three_qubit_w_pair_zero_triple_zero

Topic: quantum   Node: c066a83c81c6

Provenance: helper lemma.

For the W-state correlation tensors, three pair-zero axes also have zero triple correlation along those axes.
-/

theorem three_qubit_w_pair_zero_triple_zero
    (a b c : Fin 3 → ℝ)
    (hab : 2*(a 0*b 0+a 1*b 1)-a 2*b 2 = 0)
    (hac : 2*(a 0*c 0+a 1*c 1)-a 2*c 2 = 0)
    (hbc : 2*(b 0*c 0+b 1*c 1)-b 2*c 2 = 0) :
    (2/3:ℝ)*((∑ i, a i*b i)*c 2+(∑ i, a i*c i)*b 2+(∑ i, b i*c i)*a 2)
      -3*a 2*b 2*c 2 = 0 := by
  simp [Fin.sum_univ_succ]
  linear_combination (c 2 / 3)*hab + (b 2 / 3)*hac + (a 2 / 3)*hbc
