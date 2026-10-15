import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianSevenRectsDefect
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.MondrianSevenRects

/-!
# mondrian_seven_rects_defect_ge

Topic: combinatorics   Node: 7171df8b4464

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Proposition 2.

Within the seven-rectangle family, the defect is always at least 280 (in particular never 0): if p, q are odd then p² − 19q² ≡ 2 (mod 4), and if both are even then 4 ∣ E with E ≠ 0, so |E| ≥ 2.
-/

theorem mondrian_seven_rects_defect_ge (p q : ℕ) (hpar : p % 2 = q % 2) (hqp : q < p)
    (hp : p < 7 * q) :
    280 ≤ mondrian_defect (mondrian_seven_rects p q) := by
  have h := mondrian_seven_rects_defect p q hpar hqp hp
  have hne : (p : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2 ≠ 0 := by
    intro hE
    have hEq : p ^ 2 = 19 * q ^ 2 := by exact_mod_cast (sub_eq_zero.mp hE)
    have hq0 : q ≠ 0 := by omega
    have hp0 : p ≠ 0 := by omega
    haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have hv := congrArg (padicValNat 19) hEq
    rw [padicValNat.pow, padicValNat.mul (by norm_num) (pow_ne_zero 2 hq0),
      padicValNat.pow, padicValNat_self] at hv
    omega
  obtain ⟨s, rfl⟩ : ∃ s, p = q + 2 * s := ⟨(p - q) / 2, by omega⟩
  have hF : ((q + 2 * s : ℕ) : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2 =
      2 * (2 * (s : ℤ) ^ 2 + 2 * q * s - 9 * q ^ 2) := by push_cast; ring
  rw [hF] at h hne
  have h1 : (1 : ℤ) ≤ |2 * (s : ℤ) ^ 2 + 2 * q * s - 9 * q ^ 2| := by
    apply Int.one_le_abs
    intro h0
    apply hne
    rw [h0, mul_zero]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2)] at h
  have h2 : (280 : ℤ) ≤ (mondrian_defect (mondrian_seven_rects (q + 2 * s) q) : ℤ) := by
    rw [h]; linarith
  exact_mod_cast h2
