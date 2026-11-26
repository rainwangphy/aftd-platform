import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_missing_color_induced_edges_le_vertices

Topic: graphs   Node: bd8145c00de8

Provenance: helper lemma. Local-state criterion for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

In any strong six-color local-state coloring, every finite set of edges induced by vertices missing a given external color has at most as many edges as vertices. Thus each missing-color induced subgraph is a pseudoforest.
-/

theorem op874_missing_color_induced_edges_le_vertices
    {V E Ω : Type*} [Fintype Ω] [DecidableEq V] [DecidableEq E]
    (hΩ : Fintype.card Ω = 6)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hcubic : ∀ v, Set.ncard {e | v ∈ ends e} = 3)
    (c h : V → E → Ω)
    (hc : ∀ v e f, v ∈ ends e → v ∈ ends f → c v e = c v f → e = f)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hch : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e ≠ c v f)
    (hs : truncation_local_states_define_strong_coloring ends c h)
    (S : Finset V) (F : Finset E) (a : Ω)
    (hends : ∀ e ∈ F, ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v))
    (hmiss : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a) : F.card ≤ S.card := by
  classical
  have compat := (truncation_local_states_strong_coloring_iff
    hΩ ends hloop hcubic c h hc hh hch).1 hs
  have cover (e : E) (heF : e ∈ F) :
      ∃ v ∈ S, v ∈ ends e ∧ h v e = a := by
    obtain ⟨u, hu, v, hv, he⟩ := hends e heF
    have hU : u ∈ ends e := by rw [he]; simp
    have hV : v ∈ ends e := by rw [he]; simp
    by_contra hn
    push_neg at hn
    have hneU : h u e ≠ a := fun h => hn u hu hU h
    have hneV : h v e ≠ a := fun h => hn v hv hV h
    have huP : a ∈ truncation_exposed_pair ends c h u e :=
      ⟨hmiss u hu, fun heq => hneU heq.symm⟩
    have hvP : a ∈ truncation_exposed_pair ends c h v e :=
      ⟨hmiss v hv, fun heq => hneV heq.symm⟩
    exact Set.disjoint_left.mp (compat e u v he).2 huP hvP
  let f : {e // e ∈ F} → {v // v ∈ S} := fun e =>
    ⟨Classical.choose (cover e e.property), (Classical.choose_spec (cover e e.property)).1⟩
  have fprop (e : {e // e ∈ F}) : (f e).val ∈ ends e.val ∧ h (f e).val e.val = a :=
    (Classical.choose_spec (cover e e.property)).2
  apply Finset.card_le_card_of_injective (f := f)
  intro e e' heq
  apply Subtype.ext
  have hp := fprop e
  have hp' := fprop e'
  have val : (f e).val = (f e').val := congrArg Subtype.val heq
  rw [← val] at hp'
  exact hh (f e).val e.val e'.val hp.1 hp'.1 (hp.2.trans hp'.2.symm)
