import AFTD.Prelude
import AFTD.Kb.Tcs.MonotoneMixtureWeight
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# monotone_distribution_telescoping_sum

Topic: information   Node: 94c97c582fe7

Provenance: helper lemma. arXiv:2610.01563 Lemma 3 (2) proof

For any sequence $P : \mathbb{N}^+ \to \mathbb{R}$ and any positive integers $n \le N$, the sum $\sum_{k=n}^N \frac{w_k}{k}$ telescopes to $P(n) - P(N+1)$.
-/

/-- Telescoping sum of w_k / k from n to N. -/
lemma monotone_distribution_telescoping_sum (P : ℕ+ → ℝ) (n N : ℕ+) (hle : n ≤ N) :
    ∑ k ∈ Finset.Icc n N, monotoneMixtureWeight P k / (k : ℝ) =
      P n - P (N + 1) := by
  classical
  let f : ℕ → ℝ := fun m => if h : 0 < m then P ⟨m, h⟩ else 0
  have hf_coe (k : ℕ+) : f (k : ℕ) = P k := by
    dsimp [f]
    rw [dif_pos k.pos]
    congr 1
  have hf_succ (k : ℕ+) : f ((k : ℕ) + 1) = P (k + 1) := by
    dsimp [f]
    congr 1
  have hterm : ∀ k ∈ Finset.Icc n N,
      monotoneMixtureWeight P k / (k : ℝ) = P k - P (k + 1) := by
    intro k hk
    rw [monotoneMixtureWeight]
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt k.pos)
    field_simp [hk0]
  have hbij :
      ∑ k ∈ Finset.Icc n N, (P k - P (k + 1)) =
        ∑ m ∈ Finset.Icc (n : ℕ) (N : ℕ), (f m - f (m + 1)) := by
    refine Finset.sum_bij (fun k _ => (k : ℕ)) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨(PNat.coe_le_coe n k).mp hk.1, (PNat.coe_le_coe k N).mp hk.2⟩
    · intro a ha b hb hab
      exact PNat.coe_inj.mp hab
    · intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨(⟨m, lt_of_lt_of_le n.pos hm.1⟩ : ℕ+), ?_, rfl⟩
      exact Finset.mem_Icc.mpr
        ⟨(PNat.coe_le_coe n (⟨m, lt_of_lt_of_le n.pos hm.1⟩ : ℕ+)).mp hm.1,
         (PNat.coe_le_coe (⟨m, lt_of_lt_of_le n.pos hm.1⟩ : ℕ+) N).mp hm.2⟩
    · intro k hk
      rw [hf_coe k, hf_succ k]
  have hleNat : (n : ℕ) ≤ (N : ℕ) := (PNat.coe_le_coe n N).mpr hle
  calc
    ∑ k ∈ Finset.Icc n N, monotoneMixtureWeight P k / (k : ℝ)
        = ∑ k ∈ Finset.Icc n N, (P k - P (k + 1)) := by
          exact Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Icc (n : ℕ) (N : ℕ), (f m - f (m + 1)) := hbij
    _ = ∑ m ∈ Finset.Icc (n : ℕ) (N : ℕ), ((-f) (m + 1) - (-f) m) := by
          apply Finset.sum_congr rfl
          intro m hm
          simp only [Pi.neg_apply]
          ring
    _ = (-f) ((N : ℕ) + 1) - (-f) (n : ℕ) := by
          exact Finset.sum_Icc_sub hleNat (fun m => -f m)
    _ = f (n : ℕ) - f ((N : ℕ) + 1) := by
          simp only [Pi.neg_apply]
          ring
    _ = P n - P (N + 1) := by rw [hf_coe n, hf_succ N]
