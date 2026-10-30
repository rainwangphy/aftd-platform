import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_crossed_uniform_family_incidence_bound

Topic: social_choice   Node: 06cad28097fb

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

For a nonempty r-uniform family F, a set A that is empty or crosses a member of F, and a subfamily B disjoint from A, let Z be the number of sets and d(a) the incidence degree. Then Z times the sum of d over A, plus (rZ-1) times the size of B, is at most (rZ-1)Z.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_crossed_uniform_family_incidence_bound
    (m r : ℕ) (hr : 0 < r) (F : Finset (Finset (Fin m))) (hF : F.Nonempty)
    (hcard : ∀ T ∈ F, T.card = r) (A : Finset (Fin m))
    (hcut : A = ∅ ∨ ∃ T ∈ F, (A ∩ T).Nonempty ∧ ¬T ⊆ A)
    (B : Finset (Finset (Fin m))) (hBF : B ⊆ F)
    (hB : ∀ T ∈ B, Disjoint A T) :
    F.card * (∑ a ∈ A, (F.filter fun T => a∈T).card) +
      (r*F.card-1)*B.card ≤ (r*F.card-1)*F.card := by
  classical
  rcases hcut with rfl | ⟨T,hTF,hAT,hTA⟩
  · simp only [sum_empty,mul_zero,zero_add]
    exact Nat.mul_le_mul_left _ (card_le_card hBF)
  · let I := F.filter fun T => (A ∩ T).Nonempty
    let s := ∑ a ∈ A, (F.filter fun T => a∈T).card
    have hcount : s = ∑ T ∈ F, (A ∩ T).card := by
      dsimp only [s]
      simp only [card_eq_sum_ones,sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      rw [← sum_filter,filter_mem_eq_inter]
    have hrestrict : (∑ T ∈ F, (A ∩ T).card) = ∑ T ∈ I, (A ∩ T).card := by
      symm
      apply sum_subset (filter_subset _ _)
      intro T hTF hTI
      apply card_eq_zero.mpr
      apply not_nonempty_iff_eq_empty.mp
      intro h
      exact hTI (mem_filter.mpr ⟨hTF,h⟩)
    have hinc : s < r*I.card := by
      rw [hcount,hrestrict]
      have hle : ∀ T ∈ I, (A ∩ T).card ≤ r := by
        intro T hT
        rw [← hcard T (mem_filter.mp hT).1]
        exact card_le_card inter_subset_right
      have hlt : (A ∩ T).card < r := by
        rw [← hcard T hTF]
        apply card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨inter_subset_right,?_⟩
        intro heq
        apply hTA
        rw [← heq]
        exact inter_subset_left
      have hsum := sum_lt_sum hle ⟨T,mem_filter.mpr ⟨hTF,hAT⟩,hlt⟩
      simpa [Nat.mul_comm] using hsum
    have hdis : Disjoint I B := by
      apply disjoint_left.mpr
      intro T hTI hTB
      obtain ⟨a,ha⟩ := (mem_filter.mp hTI).2
      obtain ⟨haA,haT⟩ := mem_inter.mp ha
      exact disjoint_left.mp (hB T hTB) haA haT
    have hIB : I.card+B.card ≤ F.card := by
      rw [← card_union_of_disjoint hdis]
      exact card_le_card (union_subset (filter_subset _ _) hBF)
    let c := r*F.card-1
    have hz : 0 < F.card := card_pos.mpr hF
    have hc : c+1 = r*F.card := Nat.sub_add_cancel (by nlinarith)
    have hx : F.card*s+F.card ≤ (c+1)*I.card := by
      calc
        F.card*s+F.card = F.card*(s+1) := by ring
        _ ≤ F.card*(r*I.card) := Nat.mul_le_mul_left _ (by omega)
        _ = (c+1)*I.card := by rw [hc]; ring
    have hy := Nat.mul_le_mul_left (c+1) hIB
    change F.card*s+c*B.card ≤ c*F.card
    nlinarith
