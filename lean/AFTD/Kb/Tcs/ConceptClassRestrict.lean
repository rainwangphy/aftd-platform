import AFTD.Prelude

/-!
# concept_class_restrict

Topic: learning   Node: 23725d35b076

Provenance: formalization of a published result. Source: arXiv:2611.26721 (Littlestone dimension and its dual), Section 2 (restriction H|_{X'}).

The restriction H|_Y of a class H of functions X → Bool to a subset Y of X: the set of functions Y → Bool obtained by restricting the members of H to Y.
-/

def concept_class_restrict {X : Type*} (H : Set (X → Bool)) (Y : Set X) : Set (Y → Bool) :=
  (fun h (y : Y) => h y.1) '' H
