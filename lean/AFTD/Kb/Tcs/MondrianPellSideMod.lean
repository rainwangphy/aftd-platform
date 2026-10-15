import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPellSide

/-!
# mondrian_pell_side_mod

Topic: combinatorics   Node: d79ad4796ac5

Provenance: helper lemma. arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Theorem 1.1 (the congruence n_j ≡ 315 mod 630); serves mondrian_pell_family_defect_280.

Every side length n_j of the family is ≡ 315 (mod 630).
-/

theorem mondrian_pell_side_mod (j : ℕ) : mondrian_pell_side j % 630 = 315 := by
  have key : ∀ j, (mondrian_pell_side j % 630 = 315 ∧ mondrian_pell_side (j + 1) % 630 = 315) ∧
      mondrian_pell_side j ≤ mondrian_pell_side (j + 1) := by
    intro j
    induction j with
    | zero => simp [mondrian_pell_side]
    | succ n ih =>
      obtain ⟨⟨h1, h2⟩, h3⟩ := ih
      have e : mondrian_pell_side (n + 2) = 340 * mondrian_pell_side (n + 1) - mondrian_pell_side n := rfl
      refine ⟨⟨h2, ?_⟩, ?_⟩ <;> rw [e] <;> omega
  exact (key j).1.1
