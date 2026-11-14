import AFTD.Prelude

/-!
# is_feasible_packing

Topic: combinatorics   Node: b72686825d81

Provenance: formalization of a published result. Source: arXiv:2611.15376 Sec. 4

A multiset M of s-subsets of Fin r is a feasible packing for parameters (r, s, t, h) if every member of M has cardinality s and every t-subset of Fin r is contained in at most h members of M.
-/

/-- A multiset M of s-subsets of Fin r is a feasible packing with respect to t-subsets and bound h if every t-subset is contained in at most h members of M. -/
def is_feasible_packing (r s t h : ℕ) (M : Multiset (Finset (Fin r))) : Prop :=
  (∀ S ∈ M, S.card = s) ∧
  ∀ T : Finset (Fin r), T.card = t → (M.filter (fun S => T ⊆ S)).card ≤ h
