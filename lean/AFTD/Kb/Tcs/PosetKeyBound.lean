import AFTD.Prelude
import AFTD.Kb.Tcs.IsCompatibleSolution
import AFTD.Kb.Tcs.CrucialWeight

/-!
# poset_key_bound

Topic: algorithms   Node: 33c5d2541338

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5, line 622

For a partial order P on Fin n and rank i, KEY(P) is the supremum over all compatible solutions s = (L, e, U) of the crucial comparisons weight a_s + b_s.
-/

/-- The KEY lower bound KEY(P) is the maximum crucial comparisons weight over all compatible solutions. -/
noncomputable def poset_key_bound {n : ℕ} (P : PartialOrder (Fin n)) (i : ℕ) : ℕ := open scoped Classical in
  sSup { w : ℕ | ∃ L e U, is_compatible_solution P i L e U ∧ w = crucial_weight P L e }
