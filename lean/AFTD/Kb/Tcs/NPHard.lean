import AFTD.Prelude
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.NondeterministicPolyTimeBounded

/-!
# NPHard

Topic: np_completeness   Node: 905d24e7ac39

A language L over an alphabet Γ is NP-hard if every language L' that is in NP Karp-reduces to L, the languages L' ranging over all alphabets Γ'.
-/

/-- NP-hardness: every language in NP Karp-reduces to L. -/
def NPHard {Γ : Type} (L : Language Γ) : Prop := ∀ (Γ' : Type) (L' : Language Γ'), NondeterministicPolyTimeBounded Γ' L' → KarpReducible Γ' Γ L' L
