import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_balanced_schedule

Topic: fair_division   Node: fbd770d18521

Provenance: formalization of a published result. Source: arXiv:2611.09685

A picking sequence of m turns among n agents is balanced if each complete block of n turns contains each agent exactly once, and the remaining final block of m mod n turns contains no repeated agent.
-/

/-- A picking sequence s : Fin m → Fin n is balanced if each complete block of n turns contains each agent once and the remaining final block has no repeats. -/
def is_balanced_schedule (n m : ℕ) (s : Fin m → Fin n) : Prop :=
  (∀ (b : ℕ) (hb : (b + 1) * n ≤ m),
    Function.Injective (fun (j : Fin n) =>
      have hj : b * n + j.val < m := by
        have : j.val < n := j.isLt
        nlinarith
      s ⟨b * n + j.val, hj⟩)) ∧
  (Function.Injective (fun (j : Fin (m % n)) =>
    have hj : n * (m / n) + j.val < m := by
      have : j.val < m % n := j.isLt
      have hdiv : n * (m / n) + m % n = m := Nat.div_add_mod m n
      omega
    s ⟨n * (m / n) + j.val, hj⟩))
