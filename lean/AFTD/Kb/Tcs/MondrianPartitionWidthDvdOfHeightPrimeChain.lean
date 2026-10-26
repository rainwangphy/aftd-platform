import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionIsolatedHeightResidue
import AFTD.Kb.Tcs.MondrianPerfectHeightInjective
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_partition_width_dvd_of_height_prime_chain

Topic: combinatorics   Node: 7742d0d4d00d

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

Suppose d divides the square side and all tiles whose widths are indivisible by d have heights C times powers of a fixed prime p, with positive C. In a perfect admissible partition every tile width is divisible by d.
-/

theorem mondrian_partition_width_dvd_of_height_prime_chain (n d p C : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hz : mondrian_defect P = 0)
    (hdn : d ∣ n) (hp : Nat.Prime p) (hC : 0 < C)
    (hheight : ∀ r ∈ P, ¬ d ∣ mondrian_rect_width r →
      ∃ a, mondrian_rect_height r = C * p ^ a) :
    ∀ r ∈ P, d ∣ mondrian_rect_width r := by
  have hp0 := hp.pos
  by_contra hh
  push_neg at hh
  obtain ⟨r, hr, hrd⟩ := hh
  let S := P.toFinset.filter (fun s => ¬ d ∣ mondrian_rect_width s)
  have hS : S.Nonempty := ⟨r, by simp [S, hr, hrd]⟩
  obtain ⟨z, hzS, hzmin⟩ := S.exists_min_image mondrian_rect_height hS
  obtain ⟨hzP, hzd⟩ := Finset.mem_filter.mp hzS
  have hzP' : z ∈ P := List.mem_toFinset.mp hzP
  obtain ⟨a, hza⟩ := hheight z hzP' hzd
  let m := C * p ^ (a + 1)
  have hzm : ¬ m ∣ mondrian_rect_height z := by
    intro hm
    have hzpos : 0 < mondrian_rect_height z := by rw [hza]; positivity
    have hmle := Nat.le_of_dvd hzpos hm
    have hlt : mondrian_rect_height z < m := by
      rw [hza]
      dsimp [m]
      apply Nat.mul_lt_mul_of_pos_left _ hC
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by omega)
    omega
  have hothers : ∀ s ∈ P, s ≠ z → d ∣ mondrian_rect_width s ∨ m ∣ mondrian_rect_height s := by
    intro s hs hne
    by_cases hsd : d ∣ mondrian_rect_width s
    · exact Or.inl hsd
    right
    obtain ⟨b, hsb⟩ := hheight s hs hsd
    have hmem : s ∈ S := by simp [S, hs, hsd]
    have hle := hzmin s hmem
    have hneq : mondrian_rect_height z ≠ mondrian_rect_height s := by
      intro he
      exact hne (mondrian_perfect_height_injective n P hP hz z hzP' s hs he).symm
    have hab : a < b := by
      have hlt : C * p ^ a < C * p ^ b := by rw [← hza, ← hsb]; omega
      have hpow : p ^ a < p ^ b := by nlinarith
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpow
    rw [hsb]
    apply Nat.mul_dvd_mul_left
    exact pow_dvd_pow p (by omega : a + 1 ≤ b)
  exact hzd (mondrian_partition_isolated_height_residue n d m P hP hdn z hzP' hzm hothers)
