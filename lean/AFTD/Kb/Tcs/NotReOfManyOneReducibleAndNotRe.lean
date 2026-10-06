import AFTD.Prelude
import AFTD.Kb.Tcs.ReOfManyOneReducible

/-!
# not_re_of_manyOneReducible_and_not_re

Topic: computability   Node: 19c2634ce754

Provenance: formalization of a published result. Source: standard textbook result (computability theory: non-RE-ness transfers along many-one reductions)

If p is many-one reducible to q and p is not recursively enumerable, then q is not recursively enumerable.
-/

/-- If p reduces to q and p is not RE, then q is not RE. -/
theorem not_re_of_manyOneReducible_and_not_re {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} (h : p ≤₀ q) (hp : ¬REPred p) : ¬REPred q := by
  intro hq
  exact hp (re_of_manyOneReducible h hq)
