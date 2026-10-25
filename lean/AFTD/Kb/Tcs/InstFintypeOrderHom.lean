import AFTD.Prelude

/-!
# inst_fintype_orderHom

Topic: combinatorics   Node: 414d9fb8ab2f

Provenance: helper lemma. step towards op314_poset_tower_two_cancellation

The type of order-preserving maps between two finite partial orders is finite.
-/

/-- Finiteness of the poset of order-preserving maps between finite partial orders. Mathlib has no such instance, so cardinalities of `α →o β` cannot currently be written; this supplies one. -/
noncomputable instance inst_fintype_orderHom {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β] : Fintype (α →o β) := letI := Classical.decEq α
     Fintype.ofInjective (fun f : α →o β => (f : α → β)) (fun f g h => DFunLike.coe_injective h)
