import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# has_common_subsequence

Topic: information   Node: 6cbdaa342934

Provenance: formalization of a published result. Source: arXiv:2611.21275 Section II-B

Two vectors $u, v \in \alpha^n$ have a common subsequence of length $l$ if there exist strictly increasing index sequences $i, j : \mathrm{Fin}\,l \to \mathrm{Fin}\,n$ such that $u(i(t)) = v(j(t))$ for all $t \in \mathrm{Fin}\,l$.
-/

/-- Predicate stating that two words of length n have a common subsequence of length l. -/
def has_common_subsequence {n : ℕ} {α : Type*} (u v : Fin n → α) (l : ℕ) : Prop := ∃ (i : Fin l → Fin n) (j : Fin l → Fin n), StrictMono i ∧ StrictMono j ∧ ∀ t : Fin l, u (i t) = v (j t)
