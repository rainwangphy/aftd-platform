import AFTD.Prelude

/-!
# op869_extend_predecessors

Topic: online_algorithms   Node: 44f6efbacda5

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Extend a predecessor presentation to a larger initial-segment universe, leaving added vertices isolated.
-/

/-- Extend a predecessor presentation to a larger initial-segment universe, leaving added vertices isolated. -/
def op869_extend_predecessors {n m : ℕ} (h : n ≤ m) (P : Fin n → Finset (Fin n))
    (v : Fin m) : Finset (Fin m) :=
  if hv : v.val < n then (P ⟨v.val, hv⟩).map (Fin.castLEEmb h) else ∅
