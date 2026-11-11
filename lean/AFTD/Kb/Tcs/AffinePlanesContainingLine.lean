import AFTD.Prelude
import AFTD.Kb.Tcs.AffinePlane

/-!
# affine_planes_containing_line

Topic: combinatorics   Node: f2bf1805b8da

Provenance: formalization of a published result. Source: arXiv:2611.12153 Lemma 2.2 -- The strong cylinder conjecture over prime fields

For a prime p with [Fact p.Prime] and a subset ℓ : Set (Fin 3 → ZMod p), affine_planes_containing_line p ℓ is defined as the Finset of subsets H : Set (Fin 3 → ZMod p) such that ℓ ⊆ H and there exist a non-zero linear functional f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p and a scalar c : ZMod p with H = affine_plane f c.
-/

open Classical in
/-- The Finset of all affine planes in (ZMod p)^3 containing a given subset ℓ. -/
noncomputable def affine_planes_containing_line (p : ℕ) [Fact p.Prime] (ℓ : Set (Fin 3 → ZMod p)) :
    Finset (Set (Fin 3 → ZMod p)) := {H : Set (Fin 3 → ZMod p) | (∃ (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p) (c : ZMod p), f ≠ 0 ∧ H = affine_plane f c) ∧ ℓ ⊆ H}.toFinset
