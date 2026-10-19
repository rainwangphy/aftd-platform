import AFTD.Prelude
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# IsValidPolicy

Topic: online_algorithms   Node: 1bd805be9af5

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

A policy is valid for a Pandora's problem instance with deadlines if it respects opening deadlines and never opens any box more than once.
-/

/-- A policy is valid for an instance if it respects deadlines and opens no box twice. -/
def IsValidPolicy (inst : PandoraDeadlineInstance) (π : AdaptivePolicy inst.n) : Prop := IsValidPolicyAux inst rfl [] π
