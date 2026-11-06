import AFTD.Prelude

/-!
# rademacher_prob

Topic: statistical_mechanics   Node: 27ec5c1762e7

Provenance: original. Related work: knowledgebase: OP-1152

For a natural number m and a predicate P on Fin m → Bool, rademacher_prob m P is the uniform probability 2^(-m) * sum_{s} 1_{P(s)}.
-/

/-- The uniform probability of a predicate on the finite space of Rademacher signs Fin m → Bool. -/
noncomputable def rademacher_prob (m : ℕ) (P : (Fin m → Bool) → Prop) : ℝ := letI : DecidablePred P := Classical.decPred P
   (∑ s : Fin m → Bool, if P s then (1 : ℝ) else 0) / (2 ^ m : ℝ)
