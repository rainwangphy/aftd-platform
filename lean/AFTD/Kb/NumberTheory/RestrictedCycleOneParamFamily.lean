import AFTD.Prelude

/-!
# restricted_cycle_one_param_family

Topic: elementary_number_theory   Node: 38209d0e6982

Provenance: formalization of a published result. Source: arXiv:2610.40342 Section 5.1

The one-parameter family of subsets of {1, ..., n} consisting of {1, ..., r, k} for r < k ≤ n together with {1, ..., r}.
-/

/-- The one-parameter family of excluded sets {1, ..., r, k} for r < k ≤ n together with {1, ..., r}. -/
def restricted_cycle_one_param_family (r n : ℕ) : Finset (Finset ℕ) := insert (Finset.Icc 1 r) ((Finset.Icc (r + 1) n).image (fun k => Finset.Icc 1 r ∪ {k}))
