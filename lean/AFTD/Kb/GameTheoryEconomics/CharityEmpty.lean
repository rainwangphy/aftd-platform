import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Charity

/-!
# charity_empty

Topic: fair_division   Node: b0da0998cb16

Provenance: helper lemma. arXiv:2611.12740 Section 2

For any natural numbers m and n, the charity of the empty allocation (fun _ => ∅) : Fin n → Finset (Fin m) equals Finset.univ.
-/

/-- Under the empty allocation, all items in Fin m remain in the charity. -/
theorem charity_empty (m n : ℕ) :
    charity (m := m) (n := n) (fun _ => ∅) = (Finset.univ : Finset (Fin m)) := by
  ext x
  simp [charity]
