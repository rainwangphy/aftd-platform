import AFTD.Prelude
import AFTD.Kb.Tcs.Op874srEnds
import AFTD.Kb.Tcs.Op874srColors
import AFTD.Kb.Tcs.Op874SingleColorAtMostOneImpossible
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_no_single_external_edge_repair

Topic: graphs   Node: 7442f88f24b6

Provenance: helper lemma. OP-874: single-edge repair obstruction, experiments 38435 and 38438.

The displayed fixed external coloring has no strong completion after changing at most one edge color.
-/

theorem op874_no_single_external_edge_repair :
    ¬ ∃ (c : Fin 12 → Fin 6) (h : Fin 8 → Fin 12 → Fin 6),
      (∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → c e = c f → e=f) ∧
      (∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874sr_ends e → v ∈ op874sr_ends f → h v e ≠ c f) ∧
      truncation_local_states_define_strong_coloring op874sr_ends (fun _ e => c e) h ∧
      (∃ e, ∀ f, f ≠ e → c f = op874sr_colors f) := by
  rintro ⟨c,h,hc,hh,hch,hs,e,he⟩
  have hn : ∀ f, op874sr_colors f ≠ 2 := by decide
  apply op874_single_color_at_most_one_impossible c h hc hh hch hs
  intro f g hf hg
  have hfe : f=e := by
    by_contra hne
    exact hn f ((he f hne).symm.trans hf)
  have hge : g=e := by
    by_contra hne
    exact hn g ((he g hne).symm.trans hg)
  exact hfe.trans hge.symm
