import AFTD.Prelude
import AFTD.Kb.Tcs.LittlestoneShatters

/-!
# littlestone_dim

Topic: learning   Node: fab3c7a20058

Provenance: formalization of a published result. Source: arXiv:2611.26721 (Littlestone dimension and its dual), Section 2, definition of Ldim (empty class convention differs: 0 here instead of −1).

The Littlestone dimension of a class H of functions X → Bool, valued in ℕ∞: the supremum of the depths d such that H shatters a complete binary tree of depth d (littlestone_shatters H d), which is ⊤ when there is no maximum. For a nonempty class this is the paper's Ldim; for the empty class the supremum is 0 (the paper sets −1 there).
-/

noncomputable def littlestone_dim {X : Type*} (H : Set (X → Bool)) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : littlestone_shatters H d), (d : ℕ∞)
