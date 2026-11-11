import AFTD.Prelude
import AFTD.Kb.Tcs.AffinePlane

/-!
# affine_planes_through

Topic: combinatorics   Node: a36e44942097

Provenance: formalization of a published result. Source: arXiv:2611.12153 Lemma 2.2 -- The strong cylinder conjecture over prime fields

For a prime p with [Fact p.Prime] and a point P : Fin 3 → ZMod p, affine_planes_through p P is defined as the Finset of subsets H : Set (Fin 3 → ZMod p) such that there exists a non-zero linear functional f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p with H = affine_plane f (f P).
-/

open Classical in
/-- The Finset of all affine planes in (ZMod p)^3 containing a given point P. -/
noncomputable def affine_planes_through (p : ℕ) [Fact p.Prime] (P : Fin 3 → ZMod p) :
    Finset (Set (Fin 3 → ZMod p)) := {H : Set (Fin 3 → ZMod p) | ∃ (f : (Fin 3 → ZMod p) →ₗ[ZMod p] ZMod p), f ≠ 0 ∧ H = affine_plane f (f P)}.toFinset
