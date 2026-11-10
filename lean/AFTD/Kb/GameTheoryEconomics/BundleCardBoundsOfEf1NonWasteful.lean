import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAllocationRule
import AFTD.Kb.GameTheoryEconomics.IsNonWastefulRule
import AFTD.Kb.GameTheoryEconomics.IsEf1Rule
import AFTD.Kb.GameTheoryEconomics.PairwiseDominates

/-!
# bundle_card_bounds_of_ef1_non_wasteful

Topic: fair_division   Node: 4160f160d8ae

Provenance: helper lemma. step towards op_1321_impossibility_extension

For any allocation rule on n agents and k * n + r objects that is non-wasteful and EF1, every agent receives either k or k + 1 objects (Lemma 2 of Chernulich and Yenmez 2026).
-/

/-- For any allocation rule on n agents and k * n + r objects that is non-wasteful and EF1, every agent receives either k or k + 1 objects. -/
theorem bundle_card_bounds_of_ef1_non_wasteful (n k r : ℕ) (hn : 0 < n) (hr : r < n)
    (f : (Fin n → LinearOrder (Fin (k * n + r))) → Fin n → Finset (Fin (k * n + r)))
    (h_alloc : is_allocation_rule f) (h_nw : is_non_wasteful_rule f) (h_ef1 : is_ef1_rule f)
    (succ : Fin n → LinearOrder (Fin (k * n + r))) (i : Fin n) :
    k ≤ (f succ i).card ∧ (f succ i).card ≤ k + 1 := by
  have h_pair : ∀ a b : Fin n, (f succ b).card ≤ (f succ a).card + 1 := by
    intro a b
    obtain ⟨S, hS_sub, hS_card, h_dom⟩ := h_ef1 succ a b
    obtain ⟨g, hg_in, hg_inj, -⟩ := h_dom
    have h_le := Finset.card_le_card_of_injOn g hg_in hg_inj
    have h_diff := Finset.card_sdiff_of_subset hS_sub
    omega
  have h_disj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (f succ) := by
    intro a _ b _ hab
    exact h_alloc succ a b hab
  have h_sum_eq := Finset.card_biUnion h_disj
  have h_nw' := h_nw succ
  rw [h_nw'] at h_sum_eq
  rw [Finset.card_univ, Fintype.card_fin] at h_sum_eq
  have h_sum : ∑ j : Fin n, (f succ j).card = k * n + r := h_sum_eq.symm
  constructor
  · -- k ≤ (f succ i).card
    have h_erase : (f succ i).card + ∑ j ∈ Finset.univ.erase i, (f succ j).card = k * n + r := by
      rw [Finset.add_sum_erase Finset.univ (fun j => (f succ j).card) (Finset.mem_univ i), h_sum]
    have h_bound : ∑ j ∈ Finset.univ.erase i, (f succ j).card ≤ (n - 1) * ((f succ i).card + 1) := by
      have h1 : ∑ j ∈ Finset.univ.erase i, (f succ j).card ≤
          (Finset.univ.erase i).card • ((f succ i).card + 1) := by
        apply Finset.sum_le_card_nsmul
        intro j _
        exact h_pair i j
      rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    by_contra! h
    have h1 : (f succ i).card + 1 ≤ k := h
    have h2 : (n - 1) * ((f succ i).card + 1) ≤ (n - 1) * k := Nat.mul_le_mul_left (n - 1) h1
    have h_split : (n - 1) * k + k = n * k := by
      have : (n - 1) * k + 1 * k = (n - 1 + 1) * k := (Nat.add_mul (n - 1) 1 k).symm
      rw [one_mul] at this
      rw [this, Nat.sub_add_cancel hn]
    have h_bound' : (f succ i).card + ∑ j ∈ Finset.univ.erase i, (f succ j).card < n * k := by
      calc (f succ i).card + ∑ j ∈ Finset.univ.erase i, (f succ j).card
        _ ≤ (f succ i).card + (n - 1) * ((f succ i).card + 1) := by omega
        _ ≤ (f succ i).card + (n - 1) * k := by omega
        _ < k + (n - 1) * k := by omega
        _ = (n - 1) * k + k := by omega
        _ = n * k := h_split
    have h_ge : n * k ≤ (f succ i).card + ∑ j ∈ Finset.univ.erase i, (f succ j).card := by
      calc n * k = k * n := mul_comm n k
      _ ≤ k * n + r := Nat.le_add_right (k * n) r
      _ = (f succ i).card + ∑ j ∈ Finset.univ.erase i, (f succ j).card := h_erase.symm
    omega
  · -- (f succ i).card ≤ k + 1
    have h_le : ∑ j : Fin n, (f succ i).card ≤ ∑ j : Fin n, ((f succ j).card + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact h_pair j i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at h_le
    rw [h_sum] at h_le
    have h1 : k * n + r + n < (k + 2) * n := by
      calc k * n + r + n < k * n + n + n := by omega
      _ = (k + 2) * n := by ring
    have h2 : n * (f succ i).card < n * (k + 2) := by
      calc n * (f succ i).card ≤ k * n + r + n := h_le
      _ < (k + 2) * n := h1
      _ = n * (k + 2) := mul_comm (k + 2) n
    have h3 : (f succ i).card < k + 2 := Nat.lt_of_mul_lt_mul_left h2
    omega
