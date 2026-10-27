import AFTD.Prelude
import AFTD.Kb.Tcs.IsCaterpillar

/-!
# is_caterpillar_isTree

Topic: graphs   Node: 7e07a24031a6

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

Every caterpillar graph is a tree.
-/

/-- Every caterpillar graph is a tree. -/
theorem is_caterpillar_isTree {V : Type*} (G : SimpleGraph V) (h : is_caterpillar G) : G.IsTree := h.1
