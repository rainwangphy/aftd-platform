import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370MaximalFreeRegionSaturation

/-!
# op1370_maximal_free_regions_incomparable

Topic: combinatorics   Node: 67e38eedc9bc

Provenance: helper lemma.

For a system reaching a valid total-size upper bound, the full compatibility regions of distinct colors are mutually strongly incomparable.
-/

open Finset

theorem op1370_maximal_free_regions_incomparable
    (n t : ℕ) (hn : 0 < n) (𝒜 : Fin t → Finset (Finset (Fin n)))
    (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜)
    (K : ℕ)
    (hupper : ∀ B : Fin t → Finset (Finset (Fin n)),
      (∀ i, is_uncomplemented (B i)) → strongly_incomparable B →
      (∑ i, (B i).card) ≤ K)
    (heq : (∑ i, (𝒜 i).card) = K)
    (i j : Fin t) (hij : i ≠ j) (S T : Finset (Fin n))
    (hS : ∀ k, k ≠ i → ∀ U ∈ 𝒜 k, ¬ S ⊆ U ∧ ¬ U ⊆ S)
    (hT : ∀ k, k ≠ j → ∀ U ∈ 𝒜 k, ¬ T ⊆ U ∧ ¬ U ⊆ T) : ¬ S ⊆ T := by
  intro hST
  have hns : S ∉ 𝒜 i := by
    intro hs
    exact (hT i hij S hs).2 hST
  have hnt : T ∉ 𝒜 j := by
    intro ht
    exact (hS j hij.symm T ht).1 hST
  have hs' : Sᶜ ∈ 𝒜 i :=
    (op1370_maximal_free_region_saturation n t hn 𝒜 hunc hinc K hupper heq i S hS).resolve_left hns
  have ht' : Tᶜ ∈ 𝒜 j :=
    (op1370_maximal_free_region_saturation n t hn 𝒜 hunc hinc K hupper heq j T hT).resolve_left hnt
  exact hinc j i hij.symm Tᶜ ht' Sᶜ hs' (Finset.compl_subset_compl.mpr hST)
