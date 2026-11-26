import AFTD.Prelude

/-!
# finite_two_appearances_system_of_distinct_representatives

Topic: combinatorics   Node: 261b90ad8fb9

Provenance: helper lemma. A direct Hall-theorem helper for the matching-cut injective port cover in OP-874.

For a finite indexed family of finite sets, if every set has at least two elements and every element occurs in at most two sets, then the family has distinct representatives.
-/

open Finset
set_option maxHeartbeats 2000000

theorem finite_two_appearances_system_of_distinct_representatives
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (sets : ι → Finset α)
    (hsize : ∀ i, 2 ≤ (sets i).card)
    (hfreq : ∀ a, (Finset.univ.filter fun i => a ∈ sets i).card ≤ 2) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ sets i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' sets).mp
  intro J
  let N := J.biUnion sets
  let d : α → ℕ := fun l => (J.filter fun i => l ∈ sets i).card
  have hd2 : ∀ l, d l ≤ 2 := by
    intro l
    calc
      d l ≤ (univ.filter fun i => l ∈ sets i).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [d,Finset.mem_filter] at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi.2
      _ ≤ 2 := hfreq l
  have hsets : ∀ i ∈ J, N.filter (fun l => l ∈ sets i) = sets i := by
    intro i hi
    ext l
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hl
      exact ⟨Finset.mem_biUnion.mpr ⟨i,hi,hl⟩,hl⟩
  have hcount : (∑ i ∈ J, (sets i).card) = ∑ l ∈ N, d l := by
    calc
      _ = ∑ i ∈ J, (N.filter fun l => l ∈ sets i).card := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsets i hi]
      _ = _ := by
        have h := @Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow ι α
          (fun i l => l ∈ sets i) J N _
        simpa [Finset.bipartiteAbove, Finset.bipartiteBelow, d] using h
  have hsmall : (∑ l ∈ N, d l) ≤ 2 * N.card := by
    calc
      _ ≤ ∑ _l ∈ N, 2 := Finset.sum_le_sum (by intro l _; exact hd2 l)
      _ = _ := by simp [mul_comm]
  have hlarge : 2 * J.card ≤ ∑ i ∈ J, (sets i).card := by
    calc
      _ = ∑ _i ∈ J, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (by intro i _; exact hsize i)
  change J.card ≤ N.card
  omega
