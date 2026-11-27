import AFTD.Prelude

/-!
# littlestone_shatters

Topic: learning   Node: 978fce641435

Provenance: formalization of a published result. Source: arXiv:2611.26721 (Littlestone dimension and its dual), Section 2 (shattered complete binary trees).

For a class H of functions X → Bool and a natural number d, H shatters a complete binary tree of depth d (internal nodes labelled by points of X, the two edges below a node labelled false and true, every root-to-leaf path realized by some h in H). Defined by recursion on d: at d = 0 it means H is nonempty; at d + 1 it means there is a point x such that both {h ∈ H | h x = false} and {h ∈ H | h x = true} shatter a tree of depth d.
-/

def littlestone_shatters {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  match d with
  | 0 => H.Nonempty
  | d + 1 => ∃ x : X, littlestone_shatters {h ∈ H | h x = false} d ∧
      littlestone_shatters {h ∈ H | h x = true} d
