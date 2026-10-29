import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetOrderingScoreLeSubsetPotential
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_subset_potential_of_ordering_bound

Topic: social_choice   Node: 5b5e07bca4f5

Provenance: helper lemma. IN-339 verification route for OP-19, extending the uniform ordering-certificate reduction and the exact strict-majority convention in Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015). Related selector formulation arXiv:2604.19851v2. This is a certificate equivalence, not a new winning-set bound or research advance.

For any finite family of challenger claims with nonnegative integer weights, if every strict candidate ranking has satisfied-claim weight at most a natural number M, there is a natural-valued potential on remaining candidate subsets satisfying all local first-candidate removal inequalities and with full-set value at most M. No outside-challenger hypothesis is needed.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

theorem condorcet_subset_potential_of_ordering_bound
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) (M : ℕ)
    (hbound : ∀ σ : Equiv.Perm (Fin m),
      (∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) ≤ M) :
    ∃ H : Finset (Fin m) → ℕ,
      (∀ A : Finset (Fin m), ∀ a ∈ A,
        (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A) ∧
      H univ ≤ M := by
  classical
  let R : Finset (Fin m) → Equiv.Perm (Fin m) → ℕ := fun A σ =>
    ∑ i, if f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, σ (f i) < σ c) then w i else 0
  let H : Finset (Fin m) → ℕ := fun A => univ.sup (R A)
  refine ⟨H, ?_, ?_⟩
  · intro A a ha
    have hne : (univ : Finset (Equiv.Perm (Fin m))).Nonempty := ⟨1, mem_univ _⟩
    obtain ⟨σ, hσ, hval⟩ := Finset.sup_mem_of_nonempty (s := univ) (f := R (A.erase a)) hne
    have hH : H (A.erase a) = R (A.erase a) σ := hval.symm
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le a.val) a.isLt
    letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
    let τ : Equiv.Perm (Fin m) := σ.trans (Fin.cycleRange (σ a))
    have hτa : τ a = 0 := by
      exact Fin.cycleRange_self (σ a)
    have htop : ∀ b, b ≠ a → τ a < τ b := by
      intro b hb
      rw [hτa]
      apply (Fin.pos_iff_ne_zero' (τ b)).mpr
      intro hzero
      apply hb
      exact τ.injective (hzero.trans hτa.symm)
    have hkeep : ∀ b c, b ≠ a → c ≠ a → σ b < σ c → τ b < τ c := by
      intro b c hb hc hbc
      have hbr : σ b ≠ σ a := fun hh => hb (σ.injective hh)
      have hcr : σ c ≠ σ a := fun hh => hc (σ.injective hh)
      change (Fin.cycleRange (σ a) (σ b)).val < (Fin.cycleRange (σ a) (σ c)).val
      by_cases hbl : σ b < σ a
      · by_cases hcl : σ c < σ a
        · rw [Fin.coe_cycleRange_of_lt hbl, Fin.coe_cycleRange_of_lt hcl]
          exact Nat.add_lt_add_right hbc 1
        · have hcg : σ a < σ c := lt_of_le_of_ne (le_of_not_gt hcl) (Ne.symm hcr)
          rw [Fin.coe_cycleRange_of_lt hbl, Fin.cycleRange_of_gt hcg]
          have hb' : (σ b).val < (σ a).val := hbl
          have hc' : (σ a).val < (σ c).val := hcg
          omega
      · have hbg : σ a < σ b := lt_of_le_of_ne (le_of_not_gt hbl) (Ne.symm hbr)
        have hcg : σ a < σ c := lt_trans hbg hbc
        rw [Fin.cycleRange_of_gt hbg, Fin.cycleRange_of_gt hcg]
        exact hbc
    have hgain :
        (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + R (A.erase a) σ ≤ R A τ := by
      dsimp only [R]
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro i _
      by_cases hl : f i = a ∧ S i ⊆ A.erase a
      · have hn : ¬(f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
            (∀ c ∈ S i, σ (f i) < σ c)) := by
          intro hh
          exact (mem_erase.mp hh.1).1 hl.1
        have ht : f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, τ (f i) < τ c) := by
          refine ⟨hl.1 ▸ ha, subset_trans hl.2 (erase_subset a A), ?_⟩
          intro c hc
          rw [hl.1]
          exact htop c (mem_erase.mp (hl.2 hc)).1
        rw [if_pos hl, if_neg hn, if_pos ht, add_zero]
      · by_cases hr : f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
            (∀ c ∈ S i, σ (f i) < σ c)
        · have ht : f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, τ (f i) < τ c) := by
            refine ⟨mem_of_mem_erase hr.1, subset_trans hr.2.1 (erase_subset a A), ?_⟩
            intro c hc
            exact hkeep (f i) c (mem_erase.mp hr.1).1
              (mem_erase.mp (hr.2.1 hc)).1 (hr.2.2 c hc)
          rw [if_neg hl, if_pos hr, if_pos ht, zero_add]
        · rw [if_neg hl, if_neg hr, zero_add]
          exact Nat.zero_le _
    rw [hH]
    exact hgain.trans (Finset.le_sup (mem_univ τ))
  · apply Finset.sup_le
    intro σ _
    simpa only [R, mem_univ, subset_univ, true_and] using hbound σ
