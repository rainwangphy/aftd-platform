import AFTD.Prelude
import AFTD.Kb.Tcs.StrongTruncationMissingColorEdgeBound
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# strong_truncation_dense_vertex_set_sees_color

Topic: graphs   Node: ce4ddf923305

Provenance: helper lemma. OP-874: dense gadget obstruction to bounded component-switch repair, experiment 38459.

A finite vertex set spanning more edges than vertices must meet every external color in a strong six-color truncation coloring.
-/

theorem strong_truncation_dense_vertex_set_sees_color
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
    (hdense : S.card < (Finset.univ.filter fun e : E =>
      ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v)).card) :
    ∃ v ∈ S, ∃ e, v ∈ ends e ∧ c v e = a := by
  classical
  by_contra hn
  have hS : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a := by
    intro v hv e he heq
    exact hn ⟨v,hv,e,he,heq⟩
  have bound := strong_truncation_missing_color_edge_bound
    hΩ ends hloop hcubic c h hc hh hch hs a S hS
  apply (Nat.not_lt_of_ge bound)
  convert hdense using 1 <;> congr 1 <;> ext x <;> simp
