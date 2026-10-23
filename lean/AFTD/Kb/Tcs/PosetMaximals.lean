import AFTD.Prelude

/-!
# poset_maximals

Topic: algorithms   Node: 8fbaf08a6742

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a partial order P on a type α and a finite subset S of α, poset_maximals P S is the subset of elements x in S such that no element y in S strictly exceeds x under P.
-/

/-- The maximal elements of a finite subset under a partial order. -/
noncomputable def poset_maximals {α : Type*} (P : PartialOrder α) (S : Finset α) : Finset α := open scoped Classical in
  S.filter (fun x => ∀ y ∈ S, @LE.le α P.toLE x y → x = y)
