import AFTD.Prelude

/-!
# condorcet_subset_potential_extend_from_closed_core

Topic: social_choice   Node: 91911cdb33f2

Provenance: helper lemma. IN-341 generic support reduction for the OP-19 potential route. An actual failing-selector map may be restricted to a subset closed under all its rooted-triple claims; a potential on such a core can then ignore irrelevant candidates. No existence of a proper closed core, no weight-dispersion theorem, and no new election bound is asserted.

A local subset-potential certificate whose challenger roots and committee members all lie in a candidate core extends to the full candidate universe by intersecting every potential argument with the core. The local inequalities and full-set cost are preserved. This is a certificate-support reduction, not an assumption that an election balance property survives restriction.
-/

open Finset
open scoped BigOperators

theorem condorcet_subset_potential_extend_from_closed_core
    (C I : Type*) [Fintype C] [DecidableEq C] [Fintype I]
    (V : Finset C) (S : I → Finset C) (f : I → C) (w : I → ℕ)
    (hS : ∀ i, S i ⊆ V) (hf : ∀ i, f i ∈ V)
    (K : Finset C → ℕ)
    (hstep : ∀ A : Finset C, A ⊆ V → ∀ a ∈ A,
      (∑ i, if f i=a ∧ S i ⊆ A.erase a then w i else 0)+K (A.erase a) ≤ K A) :
    let H := fun A : Finset C => K (A ∩ V)
    (∀ A : Finset C, ∀ a ∈ A,
      (∑ i, if f i=a ∧ S i ⊆ A.erase a then w i else 0)+H (A.erase a) ≤ H A) ∧
    H Finset.univ = K V := by
  dsimp only
  constructor
  · intro A a ha
    have h1 : (A.erase a) ∩ V = (A ∩ V).erase a := Finset.erase_inter a A V
    by_cases haV : a ∈ V
    · have hB : A ∩ V ⊆ V := Finset.inter_subset_right
      have haB : a ∈ A ∩ V := Finset.mem_inter.mpr ⟨ha, haV⟩
      have key := hstep (A ∩ V) hB a haB
      rw [h1]
      have hsum : (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0)
          = (∑ i, if f i = a ∧ S i ⊆ (A ∩ V).erase a then w i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiff : (S i ⊆ A.erase a) ↔ (S i ⊆ (A ∩ V).erase a) := by
          rw [← h1, Finset.subset_inter_iff]
          exact ⟨fun h => ⟨h, hS i⟩, fun h => h.1⟩
        by_cases hfa : f i = a
        · simp only [hfa, true_and]
          by_cases hsub : S i ⊆ A.erase a
          · rw [if_pos hsub, if_pos (hiff.mp hsub)]
          · rw [if_neg hsub, if_neg (fun h => hsub (hiff.mpr h))]
        · simp only [hfa, false_and, if_false]
      rw [hsum]
      exact key
    · have hfa : ∀ i, f i ≠ a := fun i h => haV (h ▸ hf i)
      have hsum0 : (∑ i, if f i = a ∧ S i ⊆ A.erase a then w i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [hfa i]
      rw [hsum0, h1]
      have hErase : (A ∩ V).erase a = A ∩ V := by
        rw [Finset.erase_eq_self]
        simp [haV]
      rw [hErase]
      simp
  · simp
