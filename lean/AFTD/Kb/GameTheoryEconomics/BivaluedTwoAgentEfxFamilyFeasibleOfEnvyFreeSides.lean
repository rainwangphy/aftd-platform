import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BivaluedTwoAgentEfxFamilyFeasible
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# bivalued_two_agent_efx_family_feasible_of_envy_free_sides

Topic: fair_division   Node: 4ff0e61f2689

Provenance: helper lemma. arXiv:2610.14994 (Section 4.2, Theorem 4.1), reduction step for bivalued_two_agent_efx_family_feasible_all

For real r > 1, positive scales a0, a1 and natural numbers n1, n2, n3, n4: if (hA) unless n1 = n3 = n4 = 0 with n2 odd there is a weight-tie family allocation with U1 ≤ U0, V0 ≤ V1 + L1 and 0 ≤ (U0 − U1) + (V1 − V0) (the conclusion of bivalued_two_agent_efx_envy_free_zero_side, for these n1..n4 and r), and (hB) unless n1 = n2 = n4 = 0 with n3 odd there is one with U1 ≤ U0 + L0, V0 ≤ V1 and 0 ≤ (U0 − U1) + (V1 − V0) (the conclusion of bivalued_two_agent_efx_envy_free_one_side), then bivalued_two_agent_efx_family_feasible n1 n2 n3 n4 r a0 a1 holds.
-/

theorem bivalued_two_agent_efx_family_feasible_of_envy_free_sides (r a0 a1 : ℝ) (hr : 1 < r)
    (h0 : 0 < a0) (h1 : 0 < a1) (n1 n2 n3 n4 : ℕ)
    (hA : ¬ (n1 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n2 % 2 = 1) →
    ∃ a b c d : ℕ, a ≤ n1 ∧ b ≤ n2 ∧ c ≤ n3 ∧ d ≤ n4 ∧
      ((b = 0 ∧ c = n3) ∨ (a = 0 ∧ b = 0 ∧ d = 0) ∨ (a = n1 ∧ c = n3 ∧ d = n4)) ∧
      (let U0 : ℝ := (a : ℝ) + (b : ℝ) + r * (c : ℝ) + r * (d : ℝ)
       let U1 : ℝ := ((n1 - a : ℕ) : ℝ) + ((n2 - b : ℕ) : ℝ) + r * ((n3 - c : ℕ) : ℝ)
         + r * ((n4 - d : ℕ) : ℝ)
       let V0 : ℝ := (a : ℝ) + r * (b : ℝ) + (c : ℝ) + r * (d : ℝ)
       let V1 : ℝ := ((n1 - a : ℕ) : ℝ) + r * ((n2 - b : ℕ) : ℝ) + ((n3 - c : ℕ) : ℝ)
         + r * ((n4 - d : ℕ) : ℝ)
       let L1 : ℝ := if a + c ≥ 1 then 1 else if b + d ≥ 1 then r else 0
       U1 ≤ U0 ∧ V0 ≤ V1 + L1 ∧ 0 ≤ (U0 - U1) + (V1 - V0)))
    (hB : ¬ (n1 = 0 ∧ n2 = 0 ∧ n4 = 0 ∧ n3 % 2 = 1) →
    ∃ a b c d : ℕ, a ≤ n1 ∧ b ≤ n2 ∧ c ≤ n3 ∧ d ≤ n4 ∧
      ((b = 0 ∧ c = n3) ∨ (a = 0 ∧ b = 0 ∧ d = 0) ∨ (a = n1 ∧ c = n3 ∧ d = n4)) ∧
      (let U0 : ℝ := (a : ℝ) + (b : ℝ) + r * (c : ℝ) + r * (d : ℝ)
       let U1 : ℝ := ((n1 - a : ℕ) : ℝ) + ((n2 - b : ℕ) : ℝ) + r * ((n3 - c : ℕ) : ℝ)
         + r * ((n4 - d : ℕ) : ℝ)
       let V0 : ℝ := (a : ℝ) + r * (b : ℝ) + (c : ℝ) + r * (d : ℝ)
       let V1 : ℝ := ((n1 - a : ℕ) : ℝ) + r * ((n2 - b : ℕ) : ℝ) + ((n3 - c : ℕ) : ℝ)
         + r * ((n4 - d : ℕ) : ℝ)
       let L0 : ℝ := if (n1 - a) + (n2 - b) ≥ 1 then 1 else if (n3 - c) + (n4 - d) ≥ 1 then r else 0
       U1 ≤ U0 + L0 ∧ V0 ≤ V1 ∧ 0 ≤ (U0 - U1) + (V1 - V0))) :
    bivalued_two_agent_efx_family_feasible n1 n2 n3 n4 r a0 a1 := by
  unfold bivalued_two_agent_efx_family_feasible
  rcases le_total a1 a0 with ha | ha
  · by_cases hs : n1 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n2 % 2 = 1
    · obtain ⟨rfl, rfl, rfl, hodd⟩ := hs
      obtain ⟨m, rfl⟩ : ∃ m, n2 = 2 * m + 1 := ⟨n2 / 2, by omega⟩
      by_cases hc : a1 * r ≤ a0
      · refine ⟨0, m + 1, 0, 0, le_refl _, by omega, le_refl _, le_refl _,
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), ?_⟩
        have e : 2 * m + 1 - (m + 1) = m := by omega
        simp only [e, Nat.sub_self, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, add_zero]
        refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> nlinarith
      · refine ⟨0, m, 0, 0, le_refl _, by omega, le_refl _, le_refl _,
          Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), ?_⟩
        have e : 2 * m + 1 - m = m + 1 := by omega
        simp only [e, Nat.sub_self, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, add_zero]
        refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> nlinarith
    · obtain ⟨a, b, c, d, ha', hb, hc, hd, hfam, h⟩ :=
        hA hs
      refine ⟨a, b, c, d, ha', hb, hc, hd, hfam, ?_⟩
      intro U0 U1 V0 V1 L0 L1
      obtain ⟨hX, hY, hXY⟩ := h
      have hL0 : 0 ≤ L0 := by
        simp only [L0]; split_ifs <;> linarith
      refine ⟨by linarith, hY, ?_⟩
      have hX' : 0 ≤ U0 - U1 := by linarith
      nlinarith
  · by_cases hs : n1 = 0 ∧ n2 = 0 ∧ n4 = 0 ∧ n3 % 2 = 1
    · obtain ⟨rfl, rfl, rfl, hodd⟩ := hs
      obtain ⟨m, rfl⟩ : ∃ m, n3 = 2 * m + 1 := ⟨n3 / 2, by omega⟩
      by_cases hc : a1 ≤ a0 * r
      · refine ⟨0, 0, m + 1, 0, le_refl _, le_refl _, by omega, le_refl _,
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), ?_⟩
        have e : 2 * m + 1 - (m + 1) = m := by omega
        simp only [e, Nat.sub_self, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, add_zero]
        refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> nlinarith
      · refine ⟨0, 0, m, 0, le_refl _, le_refl _, by omega, le_refl _,
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), ?_⟩
        have e : 2 * m + 1 - m = m + 1 := by omega
        simp only [e, Nat.sub_self, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, add_zero]
        refine ⟨?_, ?_, ?_⟩ <;> (try split_ifs) <;> nlinarith
    · obtain ⟨a, b, c, d, ha', hb, hc, hd, hfam, h⟩ :=
        hB hs
      refine ⟨a, b, c, d, ha', hb, hc, hd, hfam, ?_⟩
      intro U0 U1 V0 V1 L0 L1
      obtain ⟨hX, hY, hXY⟩ := h
      have hL1 : 0 ≤ L1 := by
        simp only [L1]; split_ifs <;> linarith
      refine ⟨hX, by linarith, ?_⟩
      have hY' : 0 ≤ V1 - V0 := by linarith
      nlinarith
