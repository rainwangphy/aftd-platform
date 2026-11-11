import AFTD.Prelude

/-!
# local_plane_weight

Topic: combinatorics   Node: c76f7c91e0ea

Provenance: formalization of a published result. Source: arXiv:2611.12153 Lemma 2.2 -- The strong cylinder conjecture over prime fields

For a prime p with [Fact p.Prime] and subsets S, H : Set (Fin 3 → ZMod p), local_plane_weight p S H is defined as the integer ((S ∩ H).ncard : ℤ) / (p : ℤ) - 1, using integer division on ℤ.
-/

open Classical in
/-- The local weight c_P(H) = |S ∩ H|/p - 1 of an affine plane H with respect to S. -/
noncomputable def local_plane_weight (p : ℕ) [Fact p.Prime] (S : Set (Fin 3 → ZMod p)) (H : Set (Fin 3 → ZMod p)) : ℤ := ((S ∩ H).ncard : ℤ) / (p : ℤ) - 1
