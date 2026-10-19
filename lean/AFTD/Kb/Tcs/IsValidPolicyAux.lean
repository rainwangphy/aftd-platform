import AFTD.Prelude
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist

/-!
# IsValidPolicyAux

Topic: online_algorithms   Node: 9d9d16571d8b

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

A policy execution is valid if it never re-opens an already opened box, respects the deadline of each opened box, and remains valid on all realization branches.
-/

/-- Auxiliary validity condition ensuring deadlines and no re-opening along branches. -/
def IsValidPolicyAux {n : ℕ} (inst : PandoraDeadlineInstance) (hn : inst.n = n)
    (opened : List (Fin n)) : AdaptivePolicy n → Prop
  | .stop => True
  | .openBox b cont =>
      b ∉ opened ∧
      (opened.length + 1 ≤ inst.deadline (hn ▸ b)) ∧
      ∀ v ∈ (inst.dist (hn ▸ b)).support, IsValidPolicyAux inst hn (b :: opened) (cont v)
