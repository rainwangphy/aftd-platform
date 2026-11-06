import AFTD.Prelude

/-!
# four_type_simultaneous_balance_counts

Topic: fair_division   Node: 1da7149df7a3

Provenance: helper lemma. Elementary arithmetic for the bivalued two-agent rounding route in IN-570.

Four type counts can be halved so that the total and each of the two high-type marginals are balanced to within one.
-/

theorem four_type_simultaneous_balance_counts(a b c d : ℕ) :
    ∃ w x y z : ℕ,
      w ≤ a ∧ x ≤ b ∧ y ≤ c ∧ z ≤ d ∧
      w+x+y+z ≤ (a+b+c+d+1)/2 ∧
      (a-w)+(b-x)+(c-y)+(d-z) ≤ (a+b+c+d+1)/2 ∧
      x+z ≤ (b+d+1)/2 ∧ (b-x)+(d-z) ≤ (b+d+1)/2 ∧
      y+z ≤ (c+d+1)/2 ∧ (c-y)+(d-z) ≤ (c+d+1)/2 := by
  have ha : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hb : b % 2 < 2 := Nat.mod_lt _ (by omega)
  have hc : c % 2 < 2 := Nat.mod_lt _ (by omega)
  have hd : d % 2 < 2 := Nat.mod_lt _ (by omega)
  interval_cases hma : a % 2 <;> interval_cases hmb : b % 2 <;>
    interval_cases hmc : c % 2 <;> interval_cases hmd : d % 2 <;>
    first
    | refine ⟨a / 2, b / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, b / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨a / 2, (b + 1) / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, b / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, c / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, c / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, (c + 1) / 2, d / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    | refine ⟨(a + 1) / 2, (b + 1) / 2, (c + 1) / 2, (d + 1) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
