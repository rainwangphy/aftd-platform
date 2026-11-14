import AFTD.Prelude

/-!
# finset_sup_zero

Topic: online_algorithms   Node: 73d0261b69c1

Provenance: formalization of a published result. Source: arXiv:2611.15711, Section 2.1

The maximum value of a function x on a finite subset s of Fin n, defined to be 0 when s is empty.
-/

open Finset in
/-- Maximum of a real-valued function over a finite set, defined as 0 on the empty set. -/
def finset_sup_zero {n : ℕ} (s : Finset (Fin n)) (x : Fin n → ℝ) : ℝ := if h : s.Nonempty then s.sup' h x else 0
