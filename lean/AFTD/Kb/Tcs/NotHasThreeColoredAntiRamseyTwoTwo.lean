import AFTD.Prelude
import AFTD.Kb.Tcs.HasThreeColoredAntiRamsey

/-!
# not_has_three_colored_anti_ramsey_two_two

Topic: combinatorics   Node: d3194f4a8979

Provenance: helper lemma. arXiv:2611.03878, Definition 2.1

The complete graph on 2 vertices does not admit a 3-edge-coloring such that every complete subgraph on 2 vertices contains edges of all three colors.
-/

/-- The complete graph on 2 vertices does not admit a 3-edge-coloring representing all three colors on every 2-clique. -/
theorem not_has_three_colored_anti_ramsey_two_two : ¬ has_three_colored_anti_ramsey 2 2 := by
  rintro ⟨c, hc⟩
  have h := hc Finset.univ (by simp)
  obtain ⟨u, -, v, -, huv, huvc⟩ := h 0
  obtain ⟨x, -, y, -, hxy, hxyc⟩ := h 1
  have key : (s(u, v) : Sym2 (Fin 2)) = s(x, y) := by
    rw [Sym2.eq_iff]
    fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;> simp_all
  rw [key] at huvc
  exact absurd (huvc.symm.trans hxyc) (by decide)
