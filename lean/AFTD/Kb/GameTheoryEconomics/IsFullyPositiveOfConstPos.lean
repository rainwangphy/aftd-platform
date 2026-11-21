import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFullyPositive
import AFTD.Kb.GameTheoryEconomics.IsIdenticallyOrderedZero

/-!
# is_fully_positive_of_const_pos

Topic: fair_division   Node: fab648b1db6b

Provenance: helper lemma. arXiv:2611.25892, proof of Lemma 2.3

For n agents and m chores, every chore c : Fin m is fully positive under the constant unit cost matrix (fun _ _ => 1) : Fin n → Fin m → ℝ.
-/

/-- Sanity lemma: constant unit costs make every chore fully positive. -/
lemma is_fully_positive_of_const_pos (n m : ℕ) (c : Fin m) :
    is_fully_positive n m (fun _ _ => (1 : ℝ)) c := by first | exact is_identically_ordered_zero | (apply is_identically_ordered_zero <;> assumption) | (apply is_identically_ordered_zero <;> simp_all) | simpa using is_identically_ordered_zero | (simp only [is_fully_positive] at *; first | exact is_identically_ordered_zero | (apply is_identically_ordered_zero <;> assumption) | (apply is_identically_ordered_zero <;> simp_all) | simpa using is_identically_ordered_zero)
