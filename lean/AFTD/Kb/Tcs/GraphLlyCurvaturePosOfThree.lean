import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvatureOfLeaf
import AFTD.Kb.Tcs.GraphLlyCurvatureOfTwins
import AFTD.Kb.Tcs.GraphLlyCurvatureComm
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# graph_lly_curvature_pos_of_three

Topic: graphs   Node: 786961abcde5

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4).

In a finite connected graph with exactly three vertices x, y, z, every edge xy has positive Lin–Lu–Yau curvature.
-/

theorem graph_lly_curvature_pos_of_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (x y z : V) (hxy : G.Adj x y)
    (hzx : z ≠ x) (hzy : z ≠ y) (hall : ∀ w, w = x ∨ w = y ∨ w = z) :
    0 < graph_lly_curvature G x y := by
  obtain ⟨p⟩ := hG.preconnected z x
  obtain ⟨w, hzw⟩ : ∃ w, G.Adj z w := by
    cases p with
    | nil => exact absurd rfl hzx
    | cons h _ => exact ⟨_, h⟩
  have hne : x ≠ y := G.ne_of_adj hxy
  by_cases ha : G.Adj x z <;> by_cases hb : G.Adj y z
  · rw [graph_lly_curvature_of_twins G hG x y hxy]
    · have : (0 : ℝ) < G.degree x := by
        exact_mod_cast (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
      positivity
    · intro v hvx hvy
      rcases hall v with h | h | h
      · exact absurd h hvx
      · exact absurd h hvy
      · subst v; exact ⟨fun _ => hb, fun _ => ha⟩
  · rw [graph_lly_curvature_comm, graph_lly_curvature_of_leaf G hG y x hxy.symm]
    · have : (0 : ℝ) < G.degree x := by
        exact_mod_cast (G.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
      positivity
    · intro v hv
      rcases hall v with h | h | h
      · exact h
      · subst v; exact absurd hv G.irrefl
      · subst v; exact absurd hv hb
  · rw [graph_lly_curvature_of_leaf G hG x y hxy]
    · have : (0 : ℝ) < G.degree y := by
        exact_mod_cast (G.degree_pos_iff_exists_adj y).mpr ⟨x, hxy.symm⟩
      positivity
    · intro v hv
      rcases hall v with h | h | h
      · subst v; exact absurd hv G.irrefl
      · exact h
      · subst v; exact absurd hv ha
  · exfalso
    rcases hall w with h | h | h
    · subst w; exact ha hzw.symm
    · subst w; exact hb hzw.symm
    · subst w; exact G.irrefl hzw
