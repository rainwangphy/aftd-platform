import AFTD.Prelude

/-!
# discrete_intervals

Topic: learning   Node: 7e2bd90ee9bf

Provenance: formalization of a published result. Source: arXiv:2611.28727 Section 1 and Figure 8

The concept class of discrete intervals on Fin m, formalized as a Finset of indicator functions Fin m → Bool, containing the constantly false function and the indicator function of {x : Fin m | a.val ≤ x.val ∧ x.val ≤ b.val} for every pair (a, b) : Fin m × Fin m with a ≤ b.
-/

/-- The concept class of discrete intervals on Fin m. -/
def discrete_intervals (m : ℕ) : Finset (Fin m → Bool) :=
  insert (fun _ => false)
  (((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≤ p.2)).image
  (fun p => fun x => decide (p.1.val ≤ x.val ∧ x.val ≤ p.2.val)))
