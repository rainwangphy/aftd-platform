import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationMissingColorInducedEdgeBound
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# strong_truncation_missing_color_edge_bound

Topic: graphs   Node: 300433294785

Provenance: helper lemma. Necessary pseudoforest condition derived from the exact local criterion in arXiv:2610.41950, Section 2, for OP-874.

In any strong six-color truncation coloring represented by valid local states on a loopless cubic multigraph, every finite set S of vertices missing color a on its external incident edges spans at most |S| base edges.
-/

theorem strong_truncation_missing_color_edge_bound
    {V E Ω : Type*} [DecidableEq V] [Fintype E] [Fintype Ω]
    (hΩ : Fintype.card Ω = 6) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (a : Ω) (S : Finset V)
    (hS : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a) :
    (Finset.univ.filter fun e : E => ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v)).card ≤ S.card := by
  apply truncation_missing_color_induced_edge_bound ends c h a S hh
  · intro e u v he
    exact ((truncation_local_states_strong_coloring_iff hΩ ends hloop hcubic c h hc hh hch).mp hs e u v he).2
  · exact hS
