import AFTD.Prelude
import AFTD.Kb.Tcs.LinearBookForcesCenter

/-!
# linear_family_bounded_transversal_kernel

Topic: graphs   Node: 399fcaab5d83

Provenance: helper lemma. Related sunflower and triangle-kernel reductions: https://link.springer.com/article/10.1007/s00453-022-00986-0 and https://arxiv.org/abs/2308.16515. This is a structural helper for the triangle packing-cover campaign, with no claim of novelty.

Given a finite linear set family, a transversal B, a subfamily P, and a cover budget q, retain P and at most q+1 sets through each point of B. Every transversal of size at most q for the retained subfamily covers the whole family.
-/

open Finset
set_option maxHeartbeats 1000000

theorem linear_family_bounded_transversal_kernel {α : Type*} [DecidableEq α]
    (H P : Finset (Finset α)) (B : Finset α) (q : ℕ)
    (hP : P ⊆ H)
    (hl : ∀ A ∈ H, ∀ D ∈ H, A ≠ D → (A ∩ D).card ≤ 1)
    (hB : ∀ A ∈ H, ¬Disjoint A B) :
    ∃ F : Finset (Finset α), F ⊆ H ∧ P ⊆ F ∧
      F.card ≤ P.card + B.card * (q + 1) ∧
      ∀ C : Finset α, C.card ≤ q →
        (∀ A ∈ F, ¬Disjoint A C) → (∀ A ∈ H, ¬Disjoint A C) := by
  classical
  have hex : ∀ b : α, ∃ R : Finset (Finset α),
      R ⊆ H.filter (fun A => b ∈ A) ∧
      R.card = min (H.filter (fun A => b ∈ A)).card (q + 1) := by
    intro b
    exact Finset.exists_subset_card_eq (min_le_left _ _)
  choose R hR hRc using hex
  let F := P ∪ B.biUnion R
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hp | hb
    · exact hP hp
    · obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hb
      exact (Finset.mem_filter.mp (hR b hb)).1
  · intro A hA
    exact Finset.mem_union_left _ hA
  · calc
      F.card ≤ P.card + (B.biUnion R).card := Finset.card_union_le _ _
      _ ≤ P.card + ∑ b ∈ B, (R b).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ P.card + B.card * (q + 1) := by
        apply Nat.add_le_add_left
        calc
          (∑ b ∈ B, (R b).card) ≤ ∑ _b ∈ B, (q + 1) := by
            apply Finset.sum_le_sum
            intro b _
            rw [hRc b]
            exact min_le_right _ _
          _ = B.card * (q + 1) := by simp
  · intro C hC hcover A hA
    by_contra hd
    obtain ⟨b, hbA, hbB⟩ := Finset.not_disjoint_iff.mp (hB A hA)
    let Q := H.filter (fun D => b ∈ D)
    have hRQ : R b ⊆ Q := hR b
    have hRcovered : ∀ D ∈ R b, ¬Disjoint D C := by
      intro D hD
      apply hcover D
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hbB, hD⟩)
    by_cases hsmall : Q.card ≤ q
    · have hEq : R b = Q := by
        apply Finset.eq_of_subset_of_card_le hRQ
        rw [hRc b]
        simp [Q, min_eq_left (Nat.le_trans hsmall (Nat.le_succ q))]
      have hAR : A ∈ R b := by
        rw [hEq]
        exact Finset.mem_filter.mpr ⟨hA, hbA⟩
      exact hRcovered A hAR hd
    · have hbig : C.card < (R b).card := by
        rw [hRc b]
        have : q + 1 ≤ Q.card := by omega
        simp only [Q, min_eq_right this]
        omega
      have hcenter : b ∈ C := by
        apply linear_book_forces_center (R b) b C
        · intro D hD
          exact (Finset.mem_filter.mp (hRQ hD)).2
        · intro D hD E hE hDE
          exact hl D (Finset.mem_filter.mp (hRQ hD)).1 E (Finset.mem_filter.mp (hRQ hE)).1 hDE
        · exact hRcovered
        · exact hbig
      exact (Finset.not_disjoint_iff.mpr ⟨b, hbA, hcenter⟩) hd
