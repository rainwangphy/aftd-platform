import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370IncomparableStrictShattering
import AFTD.Kb.Tcs.Op1370SmallFamilyShattererUncomplemented

/-!
# op_1370_small_pair_bound

Topic: combinatorics   Node: 0282c6a28eb8

Provenance: original. Related work: Sparse-pair case of arXiv:2611.12199, Conjecture 4.3; the first two families need not be uncomplemented.

For three nonempty strongly incomparable families on Fin n with n at least three, if the last family is uncomplemented and the first two together have fewer than 2^ceil(n/2) sets, then their total size is at most 2^(n-1)-1. The first two families need not be uncomplemented.
-/

open Finset
set_option maxHeartbeats 1000000

lemma op1370_local_uncomp_card (n : ℕ) (F : Finset (Finset (Fin n)))
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

theorem op_1370_small_pair_bound (n : ℕ) (hn : 3 ≤ n) (𝒜 : Fin 3 → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (hunc : is_uncomplemented (𝒜 2)) (hsmall : (𝒜 0).card + (𝒜 1).card < 2 ^ ((n + 1) / 2)) : ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  let H := 𝒜 0 ∪ 𝒜 1
  have hab : ∀ A ∈ 𝒜 0, ∀ B ∈ 𝒜 1, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
    intro A hA B hB
    exact ⟨hinc 0 1 (by decide) A hA B hB, hinc 1 0 (by decide) B hB A hA⟩
  have hd01 : Disjoint (𝒜 0) (𝒜 1) := by
    rw [Finset.disjoint_left]
    intro A hA hB
    exact (hab A hA A hB).1 (subset_refl A)
  have hHcard : H.card = (𝒜 0).card + (𝒜 1).card := Finset.card_union_of_disjoint hd01
  have hHsmall : H.card < 2 ^ ((n + 1) / 2) := by simpa [hHcard] using hsmall
  have hU : is_uncomplemented H.shatterer := op_1370_small_family_shatterer_uncomplemented n H hHsmall
  have hstrict : H.card < H.shatterer.card :=
    op_1370_incomparable_strict_shattering (𝒜 0) (𝒜 1) (hne 0) (hne 1) hab
  have hinc2 : ∀ A ∈ H, ∀ B ∈ 𝒜 2, ¬ A ⊆ B ∧ ¬ B ⊆ A := by
    intro A hA B hB
    rcases Finset.mem_union.mp hA with hA | hA
    · exact ⟨hinc 0 2 (by decide) A hA B hB, hinc 2 0 (by decide) B hB A hA⟩
    · exact ⟨hinc 1 2 (by decide) A hA B hB, hinc 2 1 (by decide) B hB A hA⟩
  have hcross : ∀ S ∈ H.shatterer, S ∉ 𝒜 2 ∧ Sᶜ ∉ 𝒜 2 := by
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
  have hdu : Disjoint H.shatterer (𝒜 2) := by
    rw [Finset.disjoint_left]
    intro S hS hS2
    exact (hcross S hS).1 hS2
  have hu : is_uncomplemented (H.shatterer ∪ 𝒜 2) := by
    intro S hS hSc
    rcases Finset.mem_union.mp hS with hS | hS
    · rcases Finset.mem_union.mp hSc with hSc | hSc
      · exact hU S hS hSc
      · exact (hcross S hS).2 hSc
    · rcases Finset.mem_union.mp hSc with hSc | hSc
      · have h := (hcross Sᶜ hSc).2
        exact h (by simpa using hS)
      · exact hunc S hS hSc
  have hsize := op1370_local_uncomp_card n (H.shatterer ∪ 𝒜 2) hu
  rw [Finset.card_union_of_disjoint hdu] at hsize
  have hn1 : 1 ≤ n := by omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at hsize
  have hsum : (∑ i, (𝒜 i).card) = (𝒜 0).card + (𝒜 1).card + (𝒜 2).card := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  omega
