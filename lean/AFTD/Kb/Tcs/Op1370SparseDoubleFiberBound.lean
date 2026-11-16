import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370PrivateElementBound
import AFTD.Kb.Tcs.Op1370PrivateAbsenceBound
import AFTD.Kb.Tcs.Op1370SparseFiberCount

/-!
# op1370_sparse_double_fiber_bound

Topic: combinatorics   Node: 02851fdacb30

Provenance: original. Related work: A conditional bound for Conjecture 4.3 of arXiv:2611.12199: at most one coordinate fiber is doubled.

Let n and t be at least three. For nonempty, uncomplemented, mutually strongly incomparable indexed families of subsets of Fin n, suppose some ground element has at most one erased fiber whose two orientations both belong to the union. Then the total size is at most 2^(n-1)-1.
-/

theorem op1370_sparse_double_fiber_bound (n t : ℕ) (hn : 3 ≤ n) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜) (x : Fin n) (hover : (((Finset.univ.biUnion 𝒜).filter (fun s => x ∉ s)) ∩ (((Finset.univ.biUnion 𝒜).filter (fun s => x ∈ s)).image (fun s => s.erase x))).card ≤ 1) : ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 1 := by
  open Finset in
  classical
  let U := univ.biUnion 𝒜
  have hdisj : ∀ i j : Fin t, i ≠ j → Disjoint (𝒜 i) (𝒜 j) := by
    intro i j hij
    rw [disjoint_left]
    intro S hSi hSj
    exact hinc i j hij S hSi S hSj (Subset.refl S)
  have hsum : U.card = ∑ i, (𝒜 i).card := by
    dsimp [U]
    rw [card_biUnion (fun i _ j _ hij => hdisj i j hij)]
  have hother : ∀ i : Fin t, ∃ j : Fin t, j ≠ i := by
    intro i
    let j : Fin t := ⟨if i.val = 0 then 1 else 0, by split <;> omega⟩
    have hj : j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j] at hv
      split at hv <;> omega
    exact ⟨j, hj⟩
  have hempty : (∅ : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, hji⟩ := hother i
    obtain ⟨T, hT⟩ := hne j
    exact hinc i j hji.symm ∅ hi T hT (empty_subset T)
  have huniv : (univ : Finset (Fin n)) ∉ U := by
    intro h
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp h
    obtain ⟨j, hji⟩ := hother i
    obtain ⟨T, hT⟩ := hne j
    exact hinc j i hji T hT univ hi (subset_univ T)
  by_cases hs : ({x} : Finset (Fin n)) ∈ U
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hs
    apply op_1370_private_element_bound n t ht 𝒜 hne hinc i x (hunc i)
    intro j hji T hT hxT
    exact hinc i j hji.symm {x} hi T hT (singleton_subset_iff.mpr hxT)
  · by_cases hv : (univ.erase x : Finset (Fin n)) ∈ U
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
      apply op_1370_private_absence_bound n t ht 𝒜 hne hinc i x (hunc i)
      intro j hji T hT
      by_contra hxT
      have hsub : T ⊆ (univ.erase x : Finset (Fin n)) := by
        intro y hy
        simp only [mem_erase, mem_univ, and_true]
        exact fun hyx => hxT (hyx ▸ hy)
      exact hinc j i hji T hT (univ.erase x) hi hsub
    · have h := op1370_sparse_fiber_count n hn U x hempty hs hv huniv hover
      rwa [hsum] at h
