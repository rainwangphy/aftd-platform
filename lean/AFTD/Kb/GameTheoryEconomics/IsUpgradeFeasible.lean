import AFTD.Prelude

/-!
# is_upgrade_feasible

Topic: fair_division   Node: b74d38ad17b0

Provenance: formalization of a published result. Source: arXiv:2611.00432, Definition 2.1

An update from an allocation A : Fin m → Fin n to an allocation A' : Fin (m + 1) → Fin n is upgrade-feasible for costs c if each agent i has an injective mapping φ from her old bundle {d : Fin m // A d = i} to her new bundle {d : Fin (m + 1) // A' d = i} such that for all d, c i (φ d) ≤ c i (Fin.castSucc d).
-/

/-- An update between two chore allocations is upgrade-feasible if each agent receives weakly less costly replacement chores. -/
def is_upgrade_feasible {m n : ℕ} (c : Fin n → Fin (m + 1) → ℝ) (A : Fin m → Fin n) (A' : Fin (m + 1) → Fin n) : Prop := ∀ i : Fin n, ∃ φ : {d : Fin m // A d = i} → {d : Fin (m + 1) // A' d = i}, Function.Injective φ ∧ ∀ d, c i (φ d).val ≤ c i (Fin.castSucc d.val)
