import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOddGirthGe

/-!
# simple_graph_odd_girth_ge_bot

Topic: graphs   Node: c766683ff2c2

Provenance: helper lemma. folklore

The empty simple graph on any vertex type has odd girth at least k for every natural number k.
-/

/-- The empty simple graph has odd girth at least k for all k. -/
theorem simple_graph_odd_girth_ge_bot {V : Type*} (k : ℕ) :
    simple_graph_odd_girth_ge (⊥ : SimpleGraph V) k := by
  intro u w hw _
  cases w with
  | nil => exact False.elim (hw.ne_nil rfl)
  | cons h _ => exact False.elim h
