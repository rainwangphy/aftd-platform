import AFTD.Prelude
import AFTD.Kb.Tcs.IsRigidSequence

/-!
# rigid_sequence_light_count_ge_m

Topic: combinatorics   Node: c795b1ba72ac

Provenance: helper lemma. arXiv:2610.35819 Proof of Theorem 4.3

Let S be a rigid sequence with parameters n and m over an additive commutative group G with m < n, such that every term in S has multiplicity n - 1 or m - 1. If W is an n-term zero-sum multiset of the form h^k l^(n-k) with 0 < k < n, where h has multiplicity n - 1 and l has multiplicity at most m - 1, then m <= n - k.
-/

/-- In a rigid sequence with light terms of multiplicity m - 1, a two-term n-term zero-sum requires at least m light terms. -/
lemma rigid_sequence_light_count_ge_m {n m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Multiset G) (hS : is_rigid_sequence n m S)
    (h_exact : ∀ x ∈ S, S.count x = n - 1 ∨ S.count x = m - 1)
    (h_elem l_elem : G) (k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    (hh : S.count h_elem = n - 1) (hl : 0 < S.count l_elem ∧ S.count l_elem ≤ m - 1)
    (W : Multiset G) (hW_card : W.card = n) (hW_sum : W.sum = 0)
    (hW_eq : W = Multiset.replicate k h_elem + Multiset.replicate (n - k) l_elem)
    (hnm : m < n) :
    m ≤ n - k := by
  by_contra h_not
  have h_lt : n - k < m := not_le.mp h_not
  have h_ne : h_elem ≠ l_elem := by
    intro h
    rw [h] at hh
    omega
  have hl_count : S.count l_elem = m - 1 := by
    have hl_mem : l_elem ∈ S := Multiset.count_pos.mp hl.1
    rcases h_exact l_elem hl_mem with h1 | h2
    · omega
    · exact h2
  have hW_le : W ≤ S := by
    rw [Multiset.le_iff_count]
    intro x
    rw [hW_eq, Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hx_h : h_elem = x
    · subst hx_h
      have : l_elem ≠ h_elem := h_ne.symm
      simp [this, hh]
      omega
    · by_cases hx_l : l_elem = x
      · subst hx_l
        simp [hx_h, hl_count]
        omega
      · simp [hx_h, hx_l]
  exact hS.1 ⟨W, hW_le, hW_card, hW_sum⟩
