import AFTD.Prelude

/-!
# op874_finite_parent_root_has_leaf

Topic: graphs   Node: 7be554350e50

Provenance: helper lemma. Finite parent-map counting lemma for the maximum-cut exchange tree.

A nonempty finite set with a root outside the parent map has a member with no child in the set.
-/

theorem op874_finite_parent_root_has_leaf {X : Type*} [DecidableEq X] (S : Finset X)
    (root : X) (parent : X → Option X) (hroot : root ∈ S) (hrootp : parent root = none) :
    ∃ a ∈ S, ∀ b ∈ S, parent b ≠ some a := by
  classical
  by_contra hn
  push_neg at hn
  let f : {a // a ∈ S} → {a // a ∈ S} := fun a =>
    ⟨Classical.choose (hn a a.property), (Classical.choose_spec (hn a a.property)).1⟩
  have hf (a : {a // a ∈ S}) : parent (f a) = some a :=
    (Classical.choose_spec (hn a a.property)).2
  have hinj : Function.Injective f := by
    intro a b hab
    have h : some a.val = some b.val := (hf a).symm.trans (congrArg parent (congrArg Subtype.val hab) |>.trans (hf b))
    apply Subtype.ext
    exact Option.some.inj h
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  obtain ⟨a, ha⟩ := hsurj ⟨root, hroot⟩
  have hp := hf a
  have : (f a).val = root := congrArg Subtype.val ha
  rw [this, hrootp] at hp
  cases hp
