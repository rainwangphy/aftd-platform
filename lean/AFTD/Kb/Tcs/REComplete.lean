import AFTD.Prelude

/-!
# REComplete

Topic: computability   Node: 46abfd6ae5ef

A predicate `p` is RE-complete if it is recursively enumerable and every recursively enumerable predicate many-one reduces to `p`.
-/

/-- A predicate on a primcodable type is RE-complete if it is RE and every RE predicate is many-one reducible to it. -/
def REComplete {α : Type*} [Primcodable α] (p : α → Prop) : Prop := REPred p ∧ ∀ {β : Type*} [Primcodable β] (q : β → Prop), REPred q → q ≤₀ p
