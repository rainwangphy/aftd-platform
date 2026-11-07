import AFTD.Prelude
import AFTD.Kb.Tcs.IsGracefulTree

/-!
# is_graceful_tree_star_two

Topic: graphs   Node: d13e43708e51

Provenance: helper lemma. arXiv:2611.01340 Section 1

The two-vertex star tree on Fin 2 is a graceful tree.
-/

/-- Sanity check: the star tree on 2 vertices (a single edge) is graceful. -/
theorem is_graceful_tree_star_two : is_graceful_tree (SimpleGraph.starGraph (0 : Fin 2)) := by
  refine ⟨SimpleGraph.isTree_starGraph 0, Equiv.refl _, ?_⟩
  intro u₁ v₁ u₂ v₂ h1 h2 _
  have : ∀ a b c d : Fin 2, a ≠ b → c ≠ d → s(a, b) = s(c, d) := by decide
  exact this u₁ v₁ u₂ v₂ h1.ne h2.ne
