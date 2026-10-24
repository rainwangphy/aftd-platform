import AFTD.Prelude
import AFTD.Kb.Tcs.Op258ChooseTwoSubPow
import AFTD.Kb.Tcs.Op258CapacityFloorGe
import AFTD.Kb.Tcs.Op258ExistsDivergentBlockIndices
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_258_exists_divergent_capacity_covering

Topic: combinatorics   Node: 7a9cf4da37f9

Provenance: helper lemma. step towards op_258_sum_ne_top_of_forces_three

If a positive antitone profile a has infinite sum in ENNReal, then for any threshold n₀, there exists l ≥ 1 with 2^l ≥ n₀, pairwise disjoint sets of colours I_j for each hypercube layer j < l, and integer capacities cap(i) ≤ a_i * C(2^l, 2) whose sum on each layer j is at least 2^{2l - 2 - j}.
-/

/-- Existence of divergent profile capacity coverings for hypercube layers. -/
theorem op_258_exists_divergent_capacity_covering
    (a : ℕ+ → ℝ) (hpos : ∀ i, 0 < a i) (hanti : Antitone a)
    (hsum : (∑' i : ℕ+, ENNReal.ofReal (a i)) = ⊤) (n₀ : ℕ) :
    ∃ (l : ℕ) (hl : 1 ≤ l) (I : Fin l → Finset ℕ+) (cap : ℕ+ → ℕ),
      n₀ ≤ 2^l ∧
      (∀ j₁ j₂ : Fin l, j₁ ≠ j₂ → Disjoint (I j₁) (I j₂)) ∧
      (∀ j : Fin l, ∀ i ∈ I j, (cap i : ℝ) ≤ a i * ((2^l).choose 2 : ℝ)) ∧
      (∀ j : Fin l, 2^(2 * l - 2 - (j : ℕ)) ≤ ∑ i ∈ I j, cap i) := by
  classical
  obtain ⟨l, hl3, r, hn0, hmono, hend, hblk⟩ :=
    op_258_exists_divergent_block_indices a hpos hanti hsum n₀
  refine ⟨l, by omega,
    fun j : Fin l => Finset.Ioc (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩),
    fun i => ⌊a i * ((2^l).choose 2 : ℝ)⌋₊, hn0, ?_, ?_, ?_⟩
  · intro j₁ j₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ioc] at hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : j₁.1 < j₂.1 := hlt
      have hle : (⟨j₁.1+1, by omega⟩ : Fin (l+1)) ≤ ⟨j₂.1, by omega⟩ := by
        rw [Fin.le_def]; exact Nat.succ_le_of_lt hlt'
      have h1 : r ⟨j₁.1 + 1, by omega⟩ ≤ r ⟨j₂.1, by omega⟩ := hmono.monotone hle
      exact (not_le.mpr hx2.1) (le_trans hx1.2 h1)
    · have hlt' : j₂.1 < j₁.1 := hgt
      have hle : (⟨j₂.1+1, by omega⟩ : Fin (l+1)) ≤ ⟨j₁.1, by omega⟩ := by
        rw [Fin.le_def]; exact Nat.succ_le_of_lt hlt'
      have h1 : r ⟨j₂.1 + 1, by omega⟩ ≤ r ⟨j₁.1, by omega⟩ := hmono.monotone hle
      exact (not_le.mpr hx1.1) (le_trans hx2.2 h1)
  · intro j i hi
    exact Nat.floor_le (mul_nonneg (le_of_lt (hpos i)) (by positivity))
  · intro j
    have hle : ∀ i ∈ Finset.Ioc (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩),
        (2:ℝ)^(2*l-2) * a i ≤ ((⌊a i * ((2^l).choose 2 : ℝ)⌋₊ : ℕ) : ℝ) := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      have hi_le : i ≤ r ⟨l, by omega⟩ := by
        have h1 : r ⟨j.1 + 1, by omega⟩ ≤ r ⟨l, by omega⟩ := by
          apply hmono.monotone
          rw [Fin.le_def]; exact Nat.succ_le_of_lt j.2
        exact le_trans hi.2 h1
      have hai : 1 / (2:ℝ)^(l-1) ≤ a i := le_trans hend (hanti hi_le)
      exact op_258_capacity_floor_ge l hl3 (a i) hai
    have hsum_le := Finset.sum_le_sum hle
    rw [← Finset.mul_sum] at hsum_le
    have key : (2:ℝ)^(2*l-2) * (1/(2:ℝ)^(j:ℕ)) ≤
        (2:ℝ)^(2*l-2) * (∑ i ∈ Finset.Ioc (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩), a i) :=
      mul_le_mul_of_nonneg_left (hblk j) (by positivity)
    have hstep : (2:ℝ)^(2*l-2) * (1/(2:ℝ)^(j:ℕ)) ≤
        ∑ i ∈ Finset.Ioc (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩),
          ((⌊a i * ((2^l).choose 2 : ℝ)⌋₊ : ℕ) : ℝ) :=
      le_trans key hsum_le
    rw [one_div, ← pow_sub₀ (2:ℝ) (by norm_num) (by omega)] at hstep
    exact_mod_cast hstep
