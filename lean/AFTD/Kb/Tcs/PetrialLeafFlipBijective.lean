import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLeafFlip

/-!
# petrial_leaf_flip_bijective

Topic: combinatorics   Node: 07d91749a429

Provenance: helper lemma. Subset-counting helper for the OP-1239 leaf recurrence.

For distinct vertices v and u, restricting a vertex subset containing v to the complement of v and toggling u is a bijection onto all subsets of that complement.
-/

open scoped symmDiff
set_option maxRecDepth 10000

theorem petrial_leaf_flip_bijective {V : Type*} [Fintype V] [DecidableEq V] (v u : V) (huv : u ≠ v) : Function.Bijective (fun F : {F : Finset V // v ∈ F} => petrial_leaf_flip v u F.1) := by
  classical
  constructor
  · intro F G h
    apply Subtype.ext
    ext x
    by_cases hx : x = v
    · subst x
      simp [F.2, G.2]
    · have hmem := congrArg (fun S => (⟨x, by simpa using hx⟩ : ({v}ᶜ : Set V)) ∈ S) h
      simp only [petrial_leaf_flip, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      by_cases hxu : x = u
      · subst x
        simp only [true_and, not_false_eq_true] at hmem
        tauto
      · simpa [hxu] using hmem
  · intro S
    let F : Finset V := insert v (S.image Subtype.val ∆ {u})
    refine ⟨⟨F, by simp [F]⟩, ?_⟩
    ext x
    have hxv : (x : V) ≠ v := x.property
    have himage : ((x : V) ∈ S.image Subtype.val) ↔ x ∈ S := by
      constructor
      · intro h
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h
        have : y = x := Subtype.ext he
        simpa [this] using hy
      · intro h
        exact Finset.mem_image.mpr ⟨x, h, rfl⟩
    simp only [petrial_leaf_flip, Finset.mem_filter, Finset.mem_univ, true_and,
      F, Finset.mem_insert, hxv, false_or, Finset.mem_symmDiff, Finset.mem_singleton, himage]
    by_cases hxu : (x : V) = u <;> simp [hxu]
