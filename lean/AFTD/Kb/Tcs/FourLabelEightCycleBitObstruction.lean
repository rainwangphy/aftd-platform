import AFTD.Prelude

/-!
# four_label_eight_cycle_bit_obstruction

Topic: combinatorics   Node: 5cb36ff0ddae

Provenance: helper lemma. Finite obstruction arising from a proposed four-label matching-contraction construction for OP-874, arXiv:2610.41950.

In the normalized four-label eight-cycle configuration, the distinctness constraints and the indicated implications on four Boolean matching bits cannot hold simultaneously.
-/

theorem four_label_eight_cycle_bit_obstruction
    (x2 x5 x6 x7 : Fin 4) (A B C D : Bool)
    (ha0 : x5 ≠ 0) (ha1 : x5 ≠ 1) (ha2 : x7 ≠ 0) (ha3 : x7 ≠ 1) (ha4 : x5 ≠ x7)
    (hb0 : x2 ≠ 2) (hb1 : x5 ≠ 2) (hb2 : x6 ≠ 2) (hb3 : x2 ≠ x5) (hb4 : x2 ≠ x6) (hb5 : x5 ≠ x6)
    (hc0 : x2 ≠ 3) (hc1 : x6 ≠ 3) (hc2 : x7 ≠ 3) (hc3 : x2 ≠ x6) (hc4 : x2 ≠ x7) (hc5 : x6 ≠ x7)
    (h0 : x7 = 2 → A ≠ D) (h1 : x2 = 0 → D ≠ B)
    (h3 : x2 = 1 → C ≠ D) (h4 : x5 = 3 → D ≠ A)
    (h5 : x6 = 1 → A ≠ B) (h7 : x6 = 0 → C ≠ A) : False := by
  have hx5 : x5 = 3 := by fin_cases x5 <;> simp_all
  have hx7 : x7 = 2 := by fin_cases x7 <;> simp_all
  have hpair : (x2 = 0 ∧ x6 = 1) ∨ (x2 = 1 ∧ x6 = 0) := by
    fin_cases x2 <;> fin_cases x6 <;> simp_all
  rcases hpair with ⟨h2,h6⟩ | ⟨h2,h6⟩
  · have had := h0 hx7
    have hdb := h1 h2
    have hab := h5 h6
    cases A <;> cases B <;> cases D <;> simp_all
  · have had := h0 hx7
    have hcd := h3 h2
    have hca := h7 h6
    cases A <;> cases C <;> cases D <;> simp_all
