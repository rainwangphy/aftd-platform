import AFTD.Prelude
import AFTD.Kb.Tcs.PosetMaximals
import AFTD.Kb.Tcs.PosetMinimals

/-!
# crucial_weight

Topic: algorithms   Node: 56168459203d

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a partial order P on Fin n and a solution with lower set L and selected element e, the crucial comparisons weight is a_s + b_s, where a_s is the number of maximal elements of L ∪ {e} minus 1, and b_s is the number of minimal elements of (Fin n) \ L minus 1.
-/

/-- The crucial comparisons weight a_s + b_s for a compatible solution (L, e, U). -/
noncomputable def crucial_weight {n : ℕ} (P : PartialOrder (Fin n))
    (L : Finset (Fin n)) (e : Fin n) : ℕ := open scoped Classical in
  ((poset_maximals P (insert e L)).card - 1) +
  ((poset_minimals P (Finset.univ \ L)).card - 1)
