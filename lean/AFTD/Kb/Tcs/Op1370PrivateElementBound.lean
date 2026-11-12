import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableStrictShattering
import AFTD.Kb.Tcs.Op1370ShatteredCapacity

/-!
# op_1370_private_element_bound

Topic: combinatorics   Node: 8e07d7717d61

Provenance: original. Related work: arXiv:2611.12199, Conjecture 4.3, for systems in which an element occurs in at most one family.

Let at least three nonempty set families on an n-element ground set be mutually strongly incomparable. Suppose some element occurs in sets from at most one family, and that family is uncomplemented. Then the total size is at most 2^(n-1)-1. No uncomplementedness hypothesis is needed for the other families.
-/

open Finset
set_option maxHeartbeats 800000

theorem op_1370_private_element_bound (n t : ℕ) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (x : Fin n) (hunc : is_uncomplemented (𝒜 i)) (hx : ∀ j, j ≠ i → ∀ S ∈ 𝒜 j, x ∉ S) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  let V : Finset (Fin n) := {x}ᶜ
  let I : Finset (Fin t) := univ.erase i
  let B : Finset (Finset (Fin n)) := I.biUnion 𝒜
  let C : Finset (Finset (Fin n)) := (𝒜 i).filter (fun s => x ∉ s)
  let D : Finset (Finset (Fin n)) := ((𝒜 i).filter (fun s => x ∈ s)).image (erase · x)
  have hB : ∀ S ∈ B, S ⊆ V := by
    intro S hS z hz
    obtain ⟨j, hj, hSj⟩ := mem_biUnion.mp hS
    have hji : j ≠ i := (mem_erase.mp hj).1
    simp only [V, mem_compl, mem_singleton]
    intro hzx
    subst z
    exact hx j hji S hSj hz
  have hC : ∀ S ∈ C, S ⊆ V := by
    intro S hS z hz
    have hnot := (mem_filter.mp hS).2
    simp only [V, mem_compl, mem_singleton]
    intro hzx
    subst z
    exact hnot hz
  have hD : ∀ S ∈ D, S ⊆ V := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    intro z hz
    simp only [V, mem_compl, mem_singleton]
    exact (mem_erase.mp hz).1
  have hCB : ∀ c ∈ C, ∀ b ∈ B, ¬ c ⊆ b ∧ ¬ b ⊆ c := by
    intro c hc b hb
    have hci := (mem_filter.mp hc).1
    obtain ⟨j, hj, hbj⟩ := mem_biUnion.mp hb
    have hji : j ≠ i := (mem_erase.mp hj).1
    exact ⟨hinc i j hji.symm c hci b hbj, hinc j i hji b hbj c hci⟩
  have hDB : ∀ d ∈ D, ∀ b ∈ B, ¬ b ⊆ d := by
    intro d hd b hb hbd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    obtain ⟨j, hj, hbj⟩ := mem_biUnion.mp hb
    have hji : j ≠ i := (mem_erase.mp hj).1
    exact hinc j i hji b hbj s (mem_filter.mp hs).1 (hbd.trans (erase_subset x s))
  have hCD : ∀ c ∈ C, V \ c ∉ D := by
    intro c hc hd
    obtain ⟨s, hs, he⟩ := mem_image.mp hd
    have hsx : x ∈ s := (mem_filter.mp hs).2
    have hcx : x ∉ c := (mem_filter.mp hc).2
    have hsc : s = cᶜ := by
      ext z
      by_cases hzx : z = x
      · subst z
        simp [hsx, hcx]
      · have hz := congrArg (fun T : Finset (Fin n) => z ∈ T) he
        simp [V, hzx] at hz ⊢
        exact hz
    apply hunc c (mem_filter.mp hc).1
    rw [← hsc]
    exact (mem_filter.mp hs).1
  have hDcard : D.card = ((𝒜 i).filter (fun s => x ∈ s)).card := by
    apply card_image_of_injOn
    intro s hs t ht he
    have hsx := (mem_filter.mp hs).2
    have htx := (mem_filter.mp ht).2
    have h := congrArg (insert x) he
    simpa [insert_erase hsx, insert_erase htx] using h
  have hCDcard : C.card + D.card = (𝒜 i).card := by
    have hh := card_filter_add_card_filter_not (s := 𝒜 i) (fun s => x ∈ s)
    change ((𝒜 i).filter (fun s => x ∈ s)).card + C.card = (𝒜 i).card at hh
    omega
  have hdisj : (↑I : Set (Fin t)).PairwiseDisjoint 𝒜 := by
    intro j hj k hk hjk
    change Disjoint (𝒜 j) (𝒜 k)
    rw [disjoint_iff_ne]
    intro A hA B hB
    rintro rfl
    exact hinc j k hjk A hA A hB (subset_refl A)
  have hBcard : B.card = ∑ j ∈ I, (𝒜 j).card := card_biUnion hdisj
  have hsum : (∑ j, (𝒜 j).card) = (𝒜 i).card + B.card := by
    have hh := add_sum_erase (univ : Finset (Fin t)) (fun j => (𝒜 j).card) (mem_univ i)
    change (𝒜 i).card + ∑ j ∈ I, (𝒜 j).card = _ at hh
    rw [← hBcard] at hh
    exact hh.symm
  have hI : 1 < I.card := by
    have : I.card = t - 1 := by simp [I]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := one_lt_card.mp hI
  let J := I.erase j
  let B' : Finset (Finset (Fin n)) := J.biUnion 𝒜
  have hBsplit : B = 𝒜 j ∪ B' := by
    calc
      B = (insert j (I.erase j)).biUnion 𝒜 := by rw [insert_erase hj]
      _ = 𝒜 j ∪ B' := by simp [B', J]
  have hB' : B'.Nonempty := by
    obtain ⟨S, hS⟩ := hne k
    refine ⟨S, mem_biUnion.mpr ⟨k, ?_, hS⟩⟩
    exact mem_erase.mpr ⟨hjk.symm, hk⟩
  have hcross : ∀ A ∈ 𝒜 j, ∀ T ∈ B', ¬ A ⊆ T ∧ ¬ T ⊆ A := by
    intro A hA T hT
    obtain ⟨k, hk, hTk⟩ := mem_biUnion.mp hT
    have hkj : k ≠ j := (mem_erase.mp hk).1
    exact ⟨hinc j k hkj.symm A hA T hTk, hinc k j hkj T hTk A hA⟩
  have hstrict : B.card < B.shatterer.card := by
    rw [hBsplit]
    exact op_1370_incomparable_strict_shattering (𝒜 j) B' (hne j) hB' hcross
  have hV : V.card = n - 1 := by simp [V, card_compl]
  have hcapacity := op_1370_shattered_capacity V B C D hB hC hD hCB hDB hCD
  rw [hV] at hcapacity
  omega
