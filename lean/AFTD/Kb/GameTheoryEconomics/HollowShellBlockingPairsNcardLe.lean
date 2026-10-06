import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBlockingPair
import AFTD.Kb.GameTheoryEconomics.HollowShellMarket
import AFTD.Kb.GameTheoryEconomics.CyclicOffset
import AFTD.Kb.GameTheoryEconomics.PermNestingBound
import AFTD.Kb.GameTheoryEconomics.CyclicOffsetEqIte

/-!
# hollow_shell_blocking_pairs_ncard_le

Topic: matching_markets   Node: d0b32f67859c

Provenance: original. Related work: answers the upper half of the Shield-Core conjecture, left open in A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem (2026), arXiv:2609.17418, Sec. 7.1; related: its Theorem 5.3 (a matching of C_n with floor((n-1)^2/4) blocking pairs) and Prop. 5.1 (displacement form); the lower half (sigma(n) >= floor((n-1)^2/4) for every profile) remains open

The upper half of the Shield-Core conjecture (arXiv:2609.17418, open): in the cyclic Hollow-Shell market C_n, every complete matching has at most floor((n-1)^2/4) blocking pairs. Theorem 5.3 of that paper gives a matching attaining floor((n-1)^2/4), so this would make it the exact maximum.
-/

/-- Upper half of the Shield-Core conjecture (arXiv:2609.17418): `β(C_n) ≤ ⌊(n-1)²/4⌋`. Open. -/
theorem hollow_shell_blocking_pairs_ncard_le (n : ℕ) (μ : Fin n ≃ Fin n) :
    {p : Fin n × Fin n | is_blocking_pair (hollow_shell_market n) μ p.1 p.2}.ncard ≤
      (n - 1) ^ 2 / 4 := by
  classical
  -- the blocking condition, unfolded
  have hset : {p : Fin n × Fin n | is_blocking_pair (hollow_shell_market n) μ p.1 p.2} =
      ↑(Finset.univ.filter fun p : Fin n × Fin n =>
        cyclic_offset p.1 p.2 + 1 < cyclic_offset p.1 (μ p.1) + 1 ∧
          n - cyclic_offset p.1 p.2 < n - cyclic_offset (μ.symm p.2) p.2) := by
    ext p
    simp [is_blocking_pair, hollow_shell_market]
  rw [hset, Set.ncard_coe_finset, Finset.card_filter, Fintype.sum_prod_type]
  -- write the woman as the partner of a man
  have hre : ∀ g : Fin n,
      (∑ h : Fin n, if cyclic_offset g h + 1 < cyclic_offset g (μ g) + 1 ∧
          n - cyclic_offset g h < n - cyclic_offset (μ.symm h) h then 1 else 0) =
      ∑ g' : Fin n, if cyclic_offset g (μ g') + 1 < cyclic_offset g (μ g) + 1 ∧
          n - cyclic_offset g (μ g') < n - cyclic_offset g' (μ g') then 1 else 0 := by
    intro g
    rw [← Equiv.sum_comp μ]
    simp only [Equiv.symm_apply_apply]
  simp only [hre]
  have hcore := perm_nesting_bound μ
  set k := ∑ b : Fin n, if (μ b : ℕ) < b then 1 else 0 with hk
  -- each blocking pair is one of the counted pairs
  have hle : (∑ g : Fin n, ∑ g' : Fin n,
      if cyclic_offset g (μ g') + 1 < cyclic_offset g (μ g) + 1 ∧
          n - cyclic_offset g (μ g') < n - cyclic_offset g' (μ g') then 1 else 0) ≤
      ∑ a : Fin n, ∑ b : Fin n,
        if ((a : ℕ) < b ∧ (μ b : ℕ) < μ a ∧ ((μ a : ℕ) < a ↔ (μ b : ℕ) < b)) ∨
          ((μ a : ℕ) < a ∧ (b : ℕ) ≤ μ b ∧ ¬((b : ℕ) < a ∧ (μ a : ℕ) < μ b)) then 1 else 0 := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have ha := a.isLt
    have hb := b.isLt
    have hpa := (μ a).isLt
    have hpb := (μ b).isLt
    have i1 : (a : ℕ) = b → (μ a : ℕ) = μ b := fun h => by rw [Fin.val_inj.mp h]
    have i2 : (μ a : ℕ) = μ b → (a : ℕ) = b := fun h => by
      rw [μ.injective (Fin.val_inj.mp h)]
    rw [cyclic_offset_eq_ite, cyclic_offset_eq_ite, cyclic_offset_eq_ite]
    by_cases h1 : (μ a : ℕ) < a <;> by_cases h2 : (μ b : ℕ) < b <;> split_ifs <;> omega
  have hkn : k ≤ n := by
    calc k ≤ ∑ _b : Fin n, 1 := by
          apply Finset.sum_le_sum; intro b _; split_ifs <;> omega
      _ = n := by simp
  obtain ⟨m, hm⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  have hnk : n - k = m := by omega
  rw [hnk] at hcore
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases m with _ | m
  · have : (∑ g : Fin n, ∑ g' : Fin n,
        if cyclic_offset g (μ g') + 1 < cyclic_offset g (μ g) + 1 ∧
          n - cyclic_offset g (μ g') < n - cyclic_offset g' (μ g') then 1 else 0) = 0 := by
      have h0 := hle
      simp only [mul_zero] at hcore
      omega
    rw [this]; exact Nat.zero_le _
  · have hB := hle.trans (by nlinarith [hcore] : _ ≤ k * m)
    have hn1 : n - 1 = k + m := by omega
    rw [hn1]
    have : ((∑ g : Fin n, ∑ g' : Fin n,
        if cyclic_offset g (μ g') + 1 < cyclic_offset g (μ g) + 1 ∧
          n - cyclic_offset g (μ g') < n - cyclic_offset g' (μ g') then 1 else 0 : ℕ) : ℤ) * 4 ≤
        ((k : ℤ) + m) ^ 2 := by
      have hB' : ((∑ g : Fin n, ∑ g' : Fin n,
          if cyclic_offset g (μ g') + 1 < cyclic_offset g (μ g) + 1 ∧
            n - cyclic_offset g (μ g') < n - cyclic_offset g' (μ g') then 1 else 0 : ℕ) : ℤ) ≤
          (k : ℤ) * m := by exact_mod_cast hB
      nlinarith [sq_nonneg ((k : ℤ) - m)]
    exact_mod_cast this
