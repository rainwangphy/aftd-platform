import AFTD.Prelude
import AFTD.Kb.Tcs.REComplete

/-!
# re_complete_of_le

Topic: computability   Node: e730d1b2e16a

If p is RE-complete, q is recursively enumerable, and p many-one reduces to q, then q is RE-complete.
-/

universe u in
/-- If p is RE-complete, q is RE, and p ≤₀ q, then q is RE-complete (for predicates in the same universe). -/
theorem re_complete_of_le {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop} (hp : REComplete.{_, u} p) (hq : REPred q) (h : p ≤₀ q) :
    REComplete.{_, u} q := ⟨hq, fun _ hr => (hp.2 _ hr).trans h⟩
