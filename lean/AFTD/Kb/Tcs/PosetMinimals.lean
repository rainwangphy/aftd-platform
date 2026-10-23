import AFTD.Prelude

/-!
# poset_minimals

Topic: algorithms   Node: cda4ef1777c9

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a partial order P on a type α and a finite subset S of α, poset_minimals P S is the subset of elements x in S such that no element y in S is strictly smaller than x under P.
-/

/-- The minimal elements of a finite subset under a partial order. -/
noncomputable def poset_minimals {α : Type*} (P : PartialOrder α) (S : Finset α) : Finset α := open scoped Classical in
  S.filter (fun x => ∀ y ∈ S, @LE.le α P.toLE y x → y = x)
