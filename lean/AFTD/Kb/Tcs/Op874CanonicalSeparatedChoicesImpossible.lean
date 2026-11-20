import AFTD.Prelude
import AFTD.Kb.Tcs.Op874CanonicalSlotInjective
import AFTD.Kb.Tcs.Op874FourteenSeparatedOwnersImpossible
import AFTD.Kb.Tcs.Op874CanonicalOwnershipData

/-!
# op874_canonical_separated_choices_impossible

Topic: combinatorics   Node: 125ddb89b4ca

Provenance: helper lemma. Modular separated-ownership obstruction, experiments 35686 and 35712.

In the explicit modular matching pattern, fourteen consumers cannot each choose one position while keeping all selected producer positions at cyclic distance at least three.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Canonical
theorem pick_injective (t : Fin 14 → Fin 3) : Function.Injective (pick t) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have hi := (t i).isLt
  have hj := (t j).isLt
  simp only [pick] at hv
  omega

end In1081Canonical
open In1081Canonical

theorem op874_canonical_separated_choices_impossible (t : Fin 14 → Fin 3)
    (hs : ∀ i j (x y : Fin 6 × Fin 7),
      In1081Canonical.slot (In1081Canonical.pick t i) = some x → In1081Canonical.slot (In1081Canonical.pick t j) = some y →
      x.1 = y.1 → y.2 ≠ x.2+1 ∧ y.2 ≠ x.2+2) : False := by
  classical
  let f : Fin 14 → Option (Fin 6 × Fin 7) := fun i => slot (pick t i)
  let S : Finset (Fin 6 × Fin 7) := Finset.univ.filter (fun x => some x ∈ Finset.univ.image f)
  have hf : Function.Injective f := op874_canonical_slot_injective.comp (pick_injective t)
  have hmem : ∀ i x, f i = some x → x ∈ S := by
    intro i x hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx⟩
  have hS : ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 → y.2 ≠ x.2+1 ∧ y.2 ≠ x.2+2 := by
    intro x hx y hy he
    have hx' : some x ∈ Finset.univ.image f := by simpa [S] using hx
    have hy' : some y ∈ Finset.univ.image f := by simpa [S] using hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx'
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy'
    exact hs i j x y hi hj he
  exact op874_fourteen_separated_owners_impossible S hS f hf hmem
