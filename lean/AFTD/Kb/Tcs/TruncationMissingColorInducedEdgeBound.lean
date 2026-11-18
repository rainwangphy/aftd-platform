import AFTD.Prelude
import AFTD.Kb.Tcs.TruncationExposedPair

/-!
# truncation_missing_color_induced_edge_bound

Topic: graphs   Node: b83f14f43080

Provenance: helper lemma. A cardinality consequence of the local signature criterion in arXiv:2610.41950, Section 2, investigated for OP-874.

Suppose that exposed color pairs at the ends of each edge are disjoint, and that the hidden colors at different edges incident with a vertex are distinct. For any color a and finite vertex set S at which a is absent from all external incident colors, at most |S| edges have both endpoints in S.
-/

set_option maxHeartbeats 5000000

theorem truncation_missing_color_induced_edge_bound
    {V E Ω : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V)
    (c h : V → E → Ω) (a : Ω) (S : Finset V)
    (hh : ∀ v e f, v ∈ ends e → v ∈ ends f → h v e = h v f → e = f)
    (hcompat : ∀ e u v, ends e = s(u,v) →
      Disjoint (truncation_exposed_pair ends c h u e) (truncation_exposed_pair ends c h v e))
    (hS : ∀ v ∈ S, ∀ e, v ∈ ends e → c v e ≠ a) :
    (Finset.univ.filter fun e : E => ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v)).card ≤ S.card := by
  classical
  let ES : Finset E := Finset.univ.filter fun e : E => ∃ u ∈ S, ∃ v ∈ S, ends e = s(u,v)
  have hw (e : E) (he : e ∈ ES) : ∃ v ∈ S, v ∈ ends e ∧ h v e = a := by
    obtain ⟨_, u, hu, v, hv, huv⟩ := Finset.mem_filter.mp he
    have hmemu : u ∈ ends e := by rw [huv]; exact Sym2.mem_mk_left u v
    have hmemv : v ∈ ends e := by rw [huv]; exact Sym2.mem_mk_right u v
    by_cases heq : h u e = a
    · exact ⟨u, hu, hmemu, heq⟩
    · refine ⟨v, hv, hmemv, ?_⟩
      by_contra hve
      have hu' : a ∈ truncation_exposed_pair ends c h u e := ⟨hS u hu, fun h' => heq h'.symm⟩
      have hv' : a ∈ truncation_exposed_pair ends c h v e := ⟨hS v hv, fun h' => hve h'.symm⟩
      exact Set.disjoint_left.mp (hcompat e u v huv) hu' hv'
  let f : {e // e ∈ ES} → {v // v ∈ S} := fun e =>
    ⟨Classical.choose (hw e.1 e.2), (Classical.choose_spec (hw e.1 e.2)).1⟩
  have hf : Function.Injective f := by
    intro e e' heq
    apply Subtype.ext
    have he := Classical.choose_spec (hw e.1 e.2)
    have he' := Classical.choose_spec (hw e'.1 e'.2)
    have hv : (f e).1 = (f e').1 := congrArg Subtype.val heq
    change Classical.choose (hw e.1 e.2) = Classical.choose (hw e'.1 e'.2) at hv
    rw [← hv] at he'
    have hd : h (f e).1 e.1 = h (f e).1 e'.1 := by
      change h (Classical.choose (hw e.1 e.2)) e.1 = h (Classical.choose (hw e.1 e.2)) e'.1
      exact he.2.2.trans he'.2.2.symm
    exact hh (f e).1 e.1 e'.1 he.2.1 he'.2.1 hd
  exact Finset.card_le_card_of_injective hf
