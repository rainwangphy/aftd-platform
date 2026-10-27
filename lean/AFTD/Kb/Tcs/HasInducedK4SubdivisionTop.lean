import AFTD.Prelude
import AFTD.Kb.Tcs.HasInducedK4Subdivision
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# has_induced_k4_subdivision_top

Topic: graphs   Node: e534655baf6d

Provenance: helper lemma. Helper for arXiv:2610.32404 Proposition 11.2 (PR-412).

The complete graph on four vertices contains an induced subdivision of K4, using the six single-edge paths.
-/

theorem has_induced_k4_subdivision_top :
    has_induced_k4_subdivision (⊤ : SimpleGraph (Fin 4)) := by
  let P : (e : {ij : Fin 4 × Fin 4 // ij.1 < ij.2}) →
      (⊤ : SimpleGraph (Fin 4)).Walk e.val.1 e.val.2 :=
    fun e => (show (⊤ : SimpleGraph (Fin 4)).Adj e.val.1 e.val.2 from
      (SimpleGraph.top_adj _ _).mpr (ne_of_lt e.property)).toWalk
  refine ⟨id, Function.injective_id, P, ?_, ?_, ?_, ?_⟩
  · intro e
    exact SimpleGraph.Adj.isPath_toWalk _
  · intro e i hi
    simpa [P] using hi
  · intro e f hef v hve hvf
    exact ⟨v, rfl⟩
  · intro x y hx hy hxy
    have hne : x ≠ y := hxy.ne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨⟨(x,y), hlt⟩, by simp [P]⟩
    · exact ⟨⟨(y,x), hgt⟩, by simp [P, Sym2.eq_swap]⟩
