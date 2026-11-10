import AFTD.Prelude

/-!
# is_splitting_system

Topic: combinatorics   Node: c8a3205f8e23

Provenance: formalization of a published result. Source: arXiv:2611.11126 Definition 1.1

A family of blocks B ⊆ 2^[n] is an (n, t)-splitting system if for every t-element subset Y ⊆ [n], there exists a block b ∈ B such that |Y ∩ b| = t / 2.
-/

/-- A family of blocks on `Fin n` is an `(n, t)`-splitting system if every subset of size `t` intersects some block in exactly `t / 2` elements. -/
def is_splitting_system (n t : ℕ) (B : Finset (Finset (Fin n))) : Prop :=
  ∀ Y ∈ (Finset.univ : Finset (Fin n)).powersetCard t, ∃ b ∈ B, (Y ∩ b).card = t / 2
