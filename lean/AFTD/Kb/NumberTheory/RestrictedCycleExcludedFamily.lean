import AFTD.Prelude

/-!
# restricted_cycle_excluded_family

Topic: elementary_number_theory   Node: 81f797201ef8

Provenance: formalization of a published result. Source: arXiv:2610.40342 Section 5.1

The family of all subsets of {1, ..., n} containing {1, ..., r}.
-/

/-- The family of subsets of {1, ..., n} containing {1, ..., r}. -/
def restricted_cycle_excluded_family (r n : ℕ) : Finset (Finset ℕ) := ((Finset.Icc (r + 1) n).powerset).image (fun T => Finset.Icc 1 r ∪ T)
