import AFTD.Prelude

/-!
# not_computable_of_manyOneReducible

Topic: computability   Node: f05e2671ffe7

If `p` is many-one reducible to `q` and `p` is undecidable (not computable), then `q` is undecidable.
-/

/-- Undecidability transfers forward under many-one reductions. -/
theorem not_computable_of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q) (h₂ : ¬ComputablePred p) : ¬ComputablePred q :=
  mt (ComputablePred.computable_of_manyOneReducible h₁) h₂
