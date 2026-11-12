import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableStrictShattering

/-!
# op_1370_uncomplemented_shatterer_others_bound

Topic: combinatorics   Node: dfa28ca4134b

Provenance: helper lemma. Reusable shattering criterion for arXiv:2611.12199, Conjecture 4.3.

For at least three nonempty mutually strongly incomparable families on Fin n, with n at least three, suppose a designated family is uncomplemented and the shattered-set family of the union of the others is also uncomplemented. Then their total size is at most 2^(n-1)-1. No uncomplementedness is needed for the individual other families.
-/

open Finset
set_option maxHeartbeats 1000000

lemma op1370_vc_uncomp_card (n : ℕ) (F : Finset (Finset (Fin n)))
    (hu : is_uncomplemented F) : 2 * F.card ≤ 2 ^ n := by
  classical
  have hd : Disjoint F (F.image compl) := by
    rw [Finset.disjoint_left]
    intro s hs hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    exact hu t ht hs
  have hi : (F.image compl).card = F.card := Finset.card_image_of_injective _ compl_injective
  have hc : (F ∪ F.image compl).card ≤ (Finset.univ : Finset (Finset (Fin n))).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd, hi] at hc
  have hh : F.card + F.card ≤ 2 ^ n := by simpa using hc
  omega

theorem op_1370_uncomplemented_shatterer_others_bound (n t : ℕ) (hn : 3 ≤ n) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (hunc : is_uncomplemented (𝒜 i)) (hSh0 : is_uncomplemented ((Finset.univ.erase i).biUnion 𝒜).shatterer) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  let I := (Finset.univ : Finset (Fin t)).erase i
  let B : Finset (Finset (Fin n)) := I.biUnion 𝒜
  have hdisj : (↑I : Set (Fin t)).PairwiseDisjoint 𝒜 := by
    intro j hj k hk hjk
    change Disjoint (𝒜 j) (𝒜 k)
    rw [disjoint_iff_ne]
    intro A hA C hC
    rintro rfl
    exact hinc j k hjk A hA A hC (subset_refl A)
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
  have hSh : is_uncomplemented B.shatterer := hSh0
  have hinc2 : ∀ A ∈ B, ∀ C ∈ 𝒜 i, ¬ A ⊆ C ∧ ¬ C ⊆ A := by
    intro A hA C hC
    obtain ⟨j, hj, hAj⟩ := mem_biUnion.mp hA
    have hji : j ≠ i := (mem_erase.mp hj).1
    exact ⟨hinc j i hji A hAj C hC, hinc i j hji.symm C hC A hAj⟩
  have hblocked : ∀ S ∈ B.shatterer, S ∉ 𝒜 i ∧ Sᶜ ∉ 𝒜 i := by
    intro S hS
    have hs := Finset.mem_shatterer.mp hS
    obtain ⟨T, hT, hST⟩ := hs.exists_superset
    constructor
    · intro hSA
      exact (hinc2 T hT S hSA).2 hST
    · intro hSc
      obtain ⟨W, hW, hSW⟩ := hs (Finset.empty_subset S)
      have hwc : W ⊆ Sᶜ := by
        intro x hx
        simp only [Finset.mem_compl]
        intro hxs
        have : x ∈ S ∩ W := Finset.mem_inter.mpr ⟨hxs, hx⟩
        rw [hSW] at this
        simpa using this
      exact (hinc2 W hW Sᶜ hSc).1 hwc
  have hdu : Disjoint B.shatterer (𝒜 i) := by
    rw [Finset.disjoint_left]
    intro S hS hSi
    exact (hblocked S hS).1 hSi
  have hu : is_uncomplemented (B.shatterer ∪ 𝒜 i) := by
    intro S hS hSc
    rcases Finset.mem_union.mp hS with hS | hS
    · rcases Finset.mem_union.mp hSc with hSc | hSc
      · exact hSh S hS hSc
      · exact (hblocked S hS).2 hSc
    · rcases Finset.mem_union.mp hSc with hSc | hSc
      · have h := (hblocked Sᶜ hSc).2
        exact h (by simpa using hS)
      · exact hunc S hS hSc
  have hsize := op1370_vc_uncomp_card n (B.shatterer ∪ 𝒜 i) hu
  rw [Finset.card_union_of_disjoint hdu] at hsize
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at hsize
  omega
