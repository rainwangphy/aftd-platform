import AFTD.Prelude

/-!
# wild_three_uniform_disjoint_pair_count

Topic: graphs   Node: 57fb780d2373

Provenance: helper lemma. IN-359 / OP-306 helper for the uniform weighted-moment route. The associated threefold triple system is standard: Compatible factorizations and three-fold triple systems (2006), construction in the proof of Theorem4.1, https://citeseerx.ist.psu.edu/document?doi=58cc9f2b7c3862f0964a05e0ac1529b9c9de8e5e&repid=rep1&type=pdf (bibliographic record https://repo.uum.edu.my/id/eprint/3494/). The graph motivation is https://arxiv.org/html/2610.22142v1, Section3.3 and the open conjecture in Section6. Incidence square sums and three-element inclusion-exclusion are ordinary finite counting. No novelty, wild-number bound, sharpness case, or research advance is claimed. Exact finite audit8955 is diagnostic, not a hypothesis.

Let T_i be three-element subsets of a finite vertex type, indexed by a finite type of size N, with repeated subsets allowed. Suppose each vertex occurs in exactly d indices and each distinct vertex pair occurs in exactly l indices. Write v for the vertex count, D for the number of ORDERED index pairs with disjoint supports, and Q for the number of ORDERED index pairs with identical supports. Then2*D=2*N^2-2*v*d^2+(v^2-v)*l^2-2*Q as an integer identity. Identical supports include different indices; Q is not merely N.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem wild_finite_incidence_intersection_square
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : ι → Finset κ) :
    (∑ i : ι, ∑ j : ι, ((T i ∩ T j).card : ℤ)) =
      ∑ a : κ, ((univ.filter fun i => a ∈ T i).card : ℤ)^2 := by
  classical
  have hcard (i j : ι) : ((T i ∩ T j).card : ℤ) =
      ∑ a : κ, (if a ∈ T i then (1 : ℤ) else 0) *
        (if a ∈ T j then (1 : ℤ) else 0) := by
    symm
    have hfilter : (univ.filter fun a : κ => a ∈ T i ∩ T j) = T i ∩ T j := by
      ext a
      simp
    calc
      _ = ∑ a : κ, if a ∈ T i ∩ T j then (1 : ℤ) else 0 := by
        apply sum_congr rfl
        intro a ha
        by_cases hi : a ∈ T i <;> by_cases hj : a ∈ T j <;> simp [hi,hj]
      _ = ((univ.filter fun a : κ => a ∈ T i ∩ T j).card : ℤ) := by
        simp [← sum_filter]
      _ = _ := by rw [hfilter]
  simp_rw [hcard]
  calc
    _ = ∑ i : ι, ∑ a : κ, ∑ j : ι,
        (if a ∈ T i then (1 : ℤ) else 0) *
          (if a ∈ T j then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro i hi
      exact sum_comm
    _ = ∑ a : κ, ∑ i : ι, ∑ j : ι,
        (if a ∈ T i then (1 : ℤ) else 0) *
          (if a ∈ T j then (1 : ℤ) else 0) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      have h : (∑ i : ι, if a ∈ T i then (1 : ℤ) else 0) =
          ((univ.filter fun i => a ∈ T i).card : ℤ) := by simp [← sum_filter]
      rw [← sum_mul_sum, ← sq, h]

theorem wild_finset_offDiag_card_int {κ : Type*} [DecidableEq κ] (S : Finset κ) :
    (S.offDiag.card : ℤ) = (S.card : ℤ)^2 - S.card := by
  have hle : S.card ≤ S.card * S.card := by
    by_cases h : S.card = 0
    · simp [h]
    · have hp : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr h
      simpa using Nat.mul_le_mul_left S.card hp
  rw [offDiag_card, Nat.cast_sub hle, Nat.cast_mul]
  ring

theorem wild_three_set_disjoint_indicator
    {κ : Type*} [DecidableEq κ] (S T : Finset κ)
    (hS : S.card = 3) (hT : T.card = 3) :
    2 * (if Disjoint S T then (1 : ℤ) else 0) =
      2 - 2 * ((S ∩ T).card : ℤ) + ((S ∩ T).offDiag.card : ℤ) -
        2 * (if S = T then (1 : ℤ) else 0) := by
  classical
  rw [wild_finset_offDiag_card_int]
  by_cases heq : S = T
  · subst T
    have hne : S ≠ ∅ := by
      intro h
      rw [h] at hS
      simp at hS
    have hnot : ¬ Disjoint S S := by
      intro h
      have hz := disjoint_iff_inter_eq_empty.mp h
      have hcard := congrArg Finset.card hz
      simp [hS] at hcard
    simp [hne,hS]
  · have hle : (S ∩ T).card ≤ 3 := by
      have h := card_le_card (inter_subset_left : S ∩ T ⊆ S)
      omega
    have hlt : (S ∩ T).card < 3 := by
      by_contra h
      have hleft : S ∩ T = S := eq_of_subset_of_card_le inter_subset_left (by omega)
      have hright : S ∩ T = T := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact heq (hleft.symm.trans hright)
    by_cases hdis : Disjoint S T
    · have hz := disjoint_iff_inter_eq_empty.mp hdis
      simp [hdis,heq,hz]
    · have hp : 0 < (S ∩ T).card := by
        by_contra h
        have hz : (S ∩ T).card = 0 := by omega
        exact hdis (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hz))
      have hcases : (S ∩ T).card = 1 ∨ (S ∩ T).card = 2 := by omega
      rcases hcases with h | h <;> norm_num [heq,hdis,h]

theorem wild_three_uniform_disjoint_pair_count
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (T : ι → Finset κ) (d l : ℕ)
    (hsize : ∀ i, (T i).card = 3)
    (hvertex : ∀ a, (univ.filter fun i => a ∈ T i).card = d)
    (hpair : ∀ a b, a ≠ b →
      (univ.filter fun i => a ∈ T i ∧ b ∈ T i).card = l) :
    2 * ((univ.filter fun p : ι × ι => Disjoint (T p.1) (T p.2)).card : ℤ) =
      2 * (Fintype.card ι : ℤ)^2 - 2 * (Fintype.card κ : ℤ) * (d : ℤ)^2 +
        ((Fintype.card κ : ℤ)^2 - Fintype.card κ) * (l : ℤ)^2 -
        2 * ((univ.filter fun p : ι × ι => T p.1 = T p.2).card : ℤ) := by
  classical
  have hinter : (∑ i : ι, ∑ j : ι, ((T i ∩ T j).card : ℤ)) =
      (Fintype.card κ : ℤ) * (d : ℤ)^2 := by
    rw [wild_finite_incidence_intersection_square]
    simp [hvertex]
  have hoff : (∑ i : ι, ∑ j : ι, ((T i ∩ T j).offDiag.card : ℤ)) =
      ((Fintype.card κ : ℤ)^2 - Fintype.card κ) * (l : ℤ)^2 := by
    simp_rw [offDiag_inter]
    rw [wild_finite_incidence_intersection_square]
    have hdeg (p : κ × κ) :
        ((univ.filter fun i => p ∈ (T i).offDiag).card : ℤ)^2 =
          if p.1 ≠ p.2 then (l : ℤ)^2 else 0 := by
      by_cases h : p.1 = p.2
      · simp [mem_offDiag,h]
      · simpa [mem_offDiag,h] using hpair p.1 p.2 h
    simp_rw [hdeg]
    have hfilter : (univ.filter fun p : κ × κ => p.1 ≠ p.2) =
        (univ : Finset κ).offDiag := by
      ext p
      simp
    calc
      _ = (((univ : Finset κ).offDiag.card : ℕ) : ℤ) * (l : ℤ)^2 := by
        rw [← hfilter]
        rw [← sum_filter]
        simp only [sum_const,nsmul_eq_mul]
      _ = _ := by rw [wild_finset_offDiag_card_int]; simp
  have hD : ((univ.filter fun p : ι × ι => Disjoint (T p.1) (T p.2)).card : ℤ) =
      ∑ i : ι, ∑ j : ι, if Disjoint (T i) (T j) then (1 : ℤ) else 0 := by
    calc
      _ = ∑ p : ι × ι, if Disjoint (T p.1) (T p.2) then (1 : ℤ) else 0 := by
        simp [← sum_filter]
      _ = _ := Fintype.sum_prod_type _
  have hQ : ((univ.filter fun p : ι × ι => T p.1 = T p.2).card : ℤ) =
      ∑ i : ι, ∑ j : ι, if T i = T j then (1 : ℤ) else 0 := by
    calc
      _ = ∑ p : ι × ι, if T p.1 = T p.2 then (1 : ℤ) else 0 := by
        simp [← sum_filter]
      _ = _ := Fintype.sum_prod_type _
  calc
    _ = ∑ i : ι, ∑ j : ι, 2 * (if Disjoint (T i) (T j) then (1 : ℤ) else 0) := by
      rw [hD]
      simp_rw [mul_sum]
    _ = ∑ i : ι, ∑ j : ι,
        (2 - 2 * ((T i ∩ T j).card : ℤ) + ((T i ∩ T j).offDiag.card : ℤ) -
          2 * (if T i = T j then (1 : ℤ) else 0)) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      exact wild_three_set_disjoint_indicator _ _ (hsize i) (hsize j)
    _ = 2 * (Fintype.card ι : ℤ)^2 -
        2 * (∑ i : ι, ∑ j : ι, ((T i ∩ T j).card : ℤ)) +
        (∑ i : ι, ∑ j : ι, ((T i ∩ T j).offDiag.card : ℤ)) -
        2 * ((univ.filter fun p : ι × ι => T p.1 = T p.2).card : ℤ) := by
      rw [hQ]
      simp only [sum_sub_distrib,sum_add_distrib]
      simp_rw [← mul_sum]
      all_goals try simp only [sum_const,card_univ,nsmul_eq_mul]
      all_goals ring
    _ = _ := by rw [hinter,hoff]; ring
