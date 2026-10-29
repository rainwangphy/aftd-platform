import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_ordering_score_le_subset_potential

Topic: social_choice   Node: eb0d3c34eb82

Provenance: helper lemma. IN-339 supporting step for the OP-19 campaign. Strict definition: Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related selector formulation: arXiv:2604.19851v2. These are verification and coalition-closure helpers; no new dimension bound or research advance is asserted.

For any finite family of challenger claims and nonnegative integer claim weights, suppose a natural-valued potential on remaining candidate subsets bounds the gain from removing any first candidate plus the potential of the remainder. Then the total weight of claims satisfied by every strict ranking is at most the potential of the full candidate set. Claims whose committee contains their challenger need no extra exclusion hypothesis.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_ordering_score_le_subset_potential
    (m q : ℕ) (S : Fin q → Finset (Fin m)) (f : Fin q → Fin m)
    (w : Fin q → ℕ) (H : Finset (Fin m) → ℕ)
    (hstep : ∀ A : Finset (Fin m), ∀ a ∈ A,
      (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) + H (A.erase a) ≤ H A)
    (σ : Equiv.Perm (Fin m)) :
    (∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) ≤ H univ := by
  classical
  have haux : ∀ A : Finset (Fin m),
      (∑ i, if f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, σ (f i) < σ c)
        then w i else 0) ≤ H A := by
    intro A
    refine Finset.strongInductionOn A ?_
    intro A ih
    by_cases hne : A.Nonempty
    · obtain ⟨a, ha, hmin⟩ := A.exists_min_image σ hne
      have hdecomp : ∀ i : Fin q,
          (f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, σ (f i) < σ c)) ↔
            (f i = a ∧ S i ⊆ A.erase a) ∨
            (f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
              (∀ c ∈ S i, σ (f i) < σ c)) := by
        intro i
        constructor
        · rintro ⟨hroot, hsub, hpref⟩
          have hnot : a ∉ S i := by
            intro hmem
            exact (not_lt_of_ge (hmin (f i) hroot)) (hpref a hmem)
          have hsub' : S i ⊆ A.erase a := by
            intro c hc
            exact mem_erase.mpr ⟨by intro heq; subst c; exact hnot hc, hsub hc⟩
          by_cases hfa : f i = a
          · exact Or.inl ⟨hfa, hsub'⟩
          · exact Or.inr ⟨mem_erase.mpr ⟨hfa, hroot⟩, hsub', hpref⟩
        · rintro (⟨hfa, hsub⟩ | ⟨hroot, hsub, hpref⟩)
          · refine ⟨hfa ▸ ha, subset_trans hsub (erase_subset a A), ?_⟩
            intro c hc
            rw [hfa]
            have hc' := mem_erase.mp (hsub hc)
            apply lt_of_le_of_ne (hmin c hc'.2)
            intro heq
            exact hc'.1 (σ.injective heq).symm
          · exact ⟨mem_of_mem_erase hroot, subset_trans hsub (erase_subset a A), hpref⟩
      have hsum :
          (∑ i, if f i ∈ A ∧ S i ⊆ A ∧ (∀ c ∈ S i, σ (f i) < σ c)
            then w i else 0) =
          (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) +
          (∑ i, if f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
            (∀ c ∈ S i, σ (f i) < σ c) then w i else 0) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        by_cases hl : f i = a ∧ S i ⊆ A.erase a
        · have hnr : ¬(f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
                (∀ c ∈ S i, σ (f i) < σ c)) := by
            intro hr
            exact (mem_erase.mp hr.1).1 hl.1
          have horig := (hdecomp i).mpr (Or.inl hl)
          rw [if_pos horig, if_pos hl, if_neg hnr, add_zero]
        · by_cases hr : f i ∈ A.erase a ∧ S i ⊆ A.erase a ∧
                (∀ c ∈ S i, σ (f i) < σ c)
          · have horig := (hdecomp i).mpr (Or.inr hr)
            rw [if_pos horig, if_neg hl, if_pos hr, zero_add]
          · have hnorig : ¬(f i ∈ A ∧ S i ⊆ A ∧
                (∀ c ∈ S i, σ (f i) < σ c)) := by
              intro hh
              exact ((hdecomp i).mp hh).elim hl hr
            rw [if_neg hnorig, if_neg hl, if_neg hr, zero_add]
      rw [hsum]
      exact le_trans (Nat.add_le_add_left (ih (A.erase a) (erase_ssubset ha)) _)
        (hstep A a ha)
    · have hA : A = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst A
      simp
  simpa only [mem_univ, subset_univ, true_and] using haux univ
