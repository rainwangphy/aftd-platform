import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# not_is_k_extendable_bot_fin_four

Topic: graphs   Node: 5bae8e5f4d64

Provenance: helper lemma. sanity lemma for is_k_extendable (arXiv:2611.22690, Section 2)

The empty graph on 4 vertices is not 1-extendable (it has no edge, hence no 1-matching).
-/

theorem not_is_k_extendable_bot_fin_four : ¬ is_k_extendable (⊥ : SimpleGraph (Fin 4)) 1 := by
  rintro ⟨-, ⟨M, hM, hc⟩, -⟩
  have : M.edgeSet = ∅ := by
    ext e; constructor
    · intro he
      exact absurd (M.edgeSet_subset he) (by simp)
    · simp
  rw [this] at hc; simp at hc
