import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianTwoChainPrefixBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_two_chain_lower_sum_lt

Topic: combinatorics   Node: 9d0749c55b26

Provenance: helper lemma. Arithmetic helper for the three-prime extension of OP-280, arXiv:2610.19193 Section 1; the superincreasing-chain route was validated in experiment 5706.

If C>0, r≥2 and p>r+1, the sum of any finite set of numbers from the chains C*p^a and C*r*p^a that are smaller than a fixed chain element x is strictly smaller than x.
-/

theorem mondrian_two_chain_lower_sum_lt (p r C x : ℕ) (hC : 0 < C) (hr : 2 ≤ r) (hpr : r + 1 < p)
    (hx : ∃ a, x = C * p ^ a ∨ x = C * r * p ^ a)
    (V : Finset ℕ) (hV : ∀ y ∈ V, ∃ a, y = C * p ^ a ∨ y = C * r * p ^ a)
    (hVlt : ∀ y ∈ V, y < x) : V.sum id < x := by
  have hp1 : 1 < p := by omega
  have hp0 : 0 < p := by omega
  let U := fun a => (Finset.range a).image (fun i => C * p ^ i) ∪
    (Finset.range a).image (fun i => C * r * p ^ i)
  have hU : ∀ a, (U a).sum id ≤ C * (r + 1) * (Finset.range a).sum (fun i => p ^ i) := by
    intro a
    have h0 : ((Finset.range a).image (fun i => C * p ^ i)).sum id ≤
        (Finset.range a).sum (fun i => C * p ^ i) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    have h1 : ((Finset.range a).image (fun i => C * r * p ^ i)).sum id ≤
        (Finset.range a).sum (fun i => C * r * p ^ i) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    have he0 : (Finset.range a).sum (fun i => C * p ^ i) =
        C * (Finset.range a).sum (fun i => p ^ i) := by rw [Finset.mul_sum]
    have he1 : (Finset.range a).sum (fun i => C * r * p ^ i) =
        C * r * (Finset.range a).sum (fun i => p ^ i) := by rw [Finset.mul_sum]
    rw [he0] at h0
    rw [he1] at h1
    have hu : ((Finset.range a).image (fun i => C * p ^ i) ∪
        (Finset.range a).image (fun i => C * r * p ^ i)).sum id +
        ((Finset.range a).image (fun i => C * p ^ i) ∩
        (Finset.range a).image (fun i => C * r * p ^ i)).sum id =
        ((Finset.range a).image (fun i => C * p ^ i)).sum id +
        ((Finset.range a).image (fun i => C * r * p ^ i)).sum id := Finset.sum_union_inter
    have hs := Nat.add_le_add h0 h1
    have he : C * (Finset.range a).sum (fun i => p ^ i) +
        C * r * (Finset.range a).sum (fun i => p ^ i) =
        C * (r + 1) * (Finset.range a).sum (fun i => p ^ i) := by ring
    rw [he] at hs
    dsimp [U]
    omega
  obtain ⟨a, hxa | hxa⟩ := hx
  · have hsub : V ⊆ U a := by
      intro y hy
      obtain ⟨b, hyb | hyb⟩ := hV y hy
      · have hba : b < a := by
          apply (Nat.pow_lt_pow_iff_right hp1).mp
          have hlt := hVlt y hy
          rw [hyb, hxa] at hlt
          nlinarith
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hba, hyb.symm⟩)
      · have hsc : C * p ^ b ≤ C * r * p ^ b := by
          have hh := Nat.mul_le_mul_left (C * p ^ b) (by omega : 1 ≤ r)
          nlinarith
        have hba : b < a := by
          apply (Nat.pow_lt_pow_iff_right hp1).mp
          have hlt := hVlt y hy
          rw [hyb, hxa] at hlt
          nlinarith
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hba, hyb.symm⟩)
    have hsum : V.sum id ≤ (U a).sum id := Finset.sum_le_sum_of_subset hsub
    have hpref := Nat.mul_lt_mul_of_pos_left (mondrian_two_chain_prefix_bound p r a hpr) hC
    have hu := hU a
    rw [hxa]
    nlinarith
  · have hsub : V ⊆ insert (C * p ^ a) (U a) := by
      intro y hy
      obtain ⟨b, hyb | hyb⟩ := hV y hy
      · have hba : b ≤ a := by
          have hlt := hVlt y hy
          rw [hyb, hxa] at hlt
          have hpow : p ^ b < p ^ (a + 1) := by
            have hh := Nat.mul_lt_mul_of_pos_right (by omega : r < p) (pow_pos hp0 a)
            rw [pow_succ]
            nlinarith
          have := (Nat.pow_lt_pow_iff_right hp1).mp hpow
          omega
        by_cases hbeq : b = a
        · rw [hyb, hbeq]
          exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr (by omega), hyb.symm⟩)
      · have hba : b < a := by
          apply (Nat.pow_lt_pow_iff_right hp1).mp
          have hlt := hVlt y hy
          rw [hyb, hxa] at hlt
          have hCr := Nat.mul_pos hC (by omega : 0 < r)
          nlinarith
        apply Finset.mem_insert_of_mem
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_range.mpr hba, hyb.symm⟩)
    have hsum : V.sum id ≤ (insert (C * p ^ a) (U a)).sum id := Finset.sum_le_sum_of_subset hsub
    have hins : (insert (C * p ^ a) (U a)).sum id ≤ C * p ^ a + (U a).sum id := by
      by_cases hh : C * p ^ a ∈ U a
      · rw [Finset.insert_eq_of_mem hh]; omega
      · simp [Finset.sum_insert hh]
    have hpref := Nat.mul_lt_mul_of_pos_left (mondrian_two_chain_prefix_bound p r a hpr) hC
    have hu := hU a
    have htwo := Nat.mul_le_mul_left (C * p ^ a) hr
    rw [hxa]
    nlinarith
