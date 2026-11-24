import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges
import AFTD.Kb.Tcs.Op874pfMissing
import AFTD.Kb.Tcs.Op874pftEnds
import AFTD.Kb.Tcs.Op874pftColor
import AFTD.Kb.Tcs.Op874PseudoforestPairrichNoPortCover
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationLocalStateInternalCover
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring

/-!
# op874_pseudoforest_fixed_external_no_strong_completion

Topic: graphs   Node: df9d710e385c

Provenance: helper lemma. OP-874: parity obstruction to completing a fixed external coloring.

For the explicit eight-vertex graph and displayed fixed external colors, no injective local hidden-color assignment disjoint from the incident external colors defines a strong coloring of the truncation.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def op874pft_lo : Fin 12 → Fin 8 := ![0,0,0,1,1,2,2,3,4,4,5,6]
private def op874pft_hi : Fin 12 → Fin 8 := ![1,3,5,2,7,3,6,4,5,7,6,7]
private def op874pft_other (v : Fin 8) (e : Fin 12) : Fin 8 :=
  if v = op874pft_lo e then op874pft_hi e else op874pft_lo e

private lemma op874pft_loopless : ∀ e, ¬ (op874pft_ends e).IsDiag := by decide
private lemma op874pft_cubic : ∀ v : Fin 8,
    Set.ncard {e : Fin 12 | v ∈ op874pft_ends e} = 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  fin_cases v <;> decide
private lemma op874pft_proper : ∀ v e f, v ∈ op874pft_ends e → v ∈ op874pft_ends f →
    op874pft_color e = op874pft_color f → e=f := by decide
private lemma op874pft_missing_iff : ∀ v z, z ∈ op874pf_missing v ↔
    ∀ e, v ∈ op874pft_ends e → op874pft_color e ≠ z := by decide
private lemma op874pft_edge_exists : ∀ u v : Fin 8, s(u,v) ∈ op874pf_edges →
    ∃ e : Fin 12, op874pft_ends e = s(u,v) := by decide
private lemma op874pft_no_loop : ∀ v : Fin 8, s(v,v) ∉ op874pf_edges := by decide
private lemma op874pft_other_edge : ∀ v e, v ∈ op874pft_ends e →
    op874pft_ends e = s(v,op874pft_other v e) := by decide
private lemma op874pft_other_inj : ∀ v e f, v ∈ op874pft_ends e → v ∈ op874pft_ends f →
    op874pft_other v e = op874pft_other v f → e=f := by decide

theorem op874_pseudoforest_fixed_external_no_strong_completion :
    ¬ ∃ h : Fin 8 → Fin 12 → Fin 6,
      (∀ v e f, v ∈ op874pft_ends e → v ∈ op874pft_ends f → h v e = h v f → e=f) ∧
      (∀ v e f, v ∈ op874pft_ends e → v ∈ op874pft_ends f → h v e ≠ op874pft_color f) ∧
      truncation_local_states_define_strong_coloring op874pft_ends
        (fun _ e => op874pft_color e) h := by
  classical
  rintro ⟨h, hh, hch, hs⟩
  let c : Fin 8 → Fin 12 → Fin 6 := fun _ e => op874pft_color e
  have hc : ∀ v e f, v ∈ op874pft_ends e → v ∈ op874pft_ends f → c v e = c v f → e=f :=
    op874pft_proper
  have compat := (truncation_local_states_strong_coloring_iff
    (by decide : Fintype.card (Fin 6)=6) op874pft_ends op874pft_loopless op874pft_cubic
    c h hc hh hch).1 hs
  have hcolor (v : Fin 8) (z : Fin 6) (hz : z ∈ op874pf_missing v) :
      ∃ e, v ∈ op874pft_ends e ∧ h v e=z := by
    apply truncation_local_state_internal_cover (by decide : Fintype.card (Fin 6)=6)
      op874pft_cubic hc hh hch
    exact (op874pft_missing_iff v z).1 hz
  let p (v : Fin 8) (z : Fin 6) : Fin 8 :=
    if hz : z ∈ op874pf_missing v then
      op874pft_other v (Classical.choose (hcolor v z hz)) else 0
  have hp (v : Fin 8) (z : Fin 6) (hz : z ∈ op874pf_missing v) :
      v ∈ op874pft_ends (Classical.choose (hcolor v z hz)) ∧
      h v (Classical.choose (hcolor v z hz)) = z ∧
      p v z = op874pft_other v (Classical.choose (hcolor v z hz)) := by
    exact ⟨(Classical.choose_spec (hcolor v z hz)).1,
      (Classical.choose_spec (hcolor v z hz)).2, by simp [p,hz]⟩
  apply op874_pseudoforest_pairrich_no_port_cover
  refine ⟨p, ?_, ?_⟩
  · intro v z w hz hw hzw hpEq
    have hz' := hp v z hz
    have hw' := hp v w hw
    have he : Classical.choose (hcolor v z hz) = Classical.choose (hcolor v w hw) :=
      op874pft_other_inj v _ _ hz'.1 hw'.1 (hz'.2.2.symm.trans (hpEq.trans hw'.2.2))
    rw [he] at hz'
    exact hzw (hz'.2.1.symm.trans hw'.2.1)
  · intro u v z he hz hv
    obtain ⟨e, heq⟩ := op874pft_edge_exists u v he
    have huv : u ≠ v := by
      intro h
      subst v
      exact op874pft_no_loop u he
    have huE : u ∈ op874pft_ends e := by rw [heq]; simp
    have hvE : v ∈ op874pft_ends e := by rw [heq]; simp
    have hcover : h u e=z ∨ h v e=z := by
      by_contra hn
      push_neg at hn
      have huP : z ∈ truncation_exposed_pair op874pft_ends c h u e :=
        ⟨(op874pft_missing_iff u z).1 hz, fun h' => hn.1 h'.symm⟩
      have hvP : z ∈ truncation_exposed_pair op874pft_ends c h v e :=
        ⟨(op874pft_missing_iff v z).1 hv, fun h' => hn.2 h'.symm⟩
      exact Set.disjoint_left.mp (compat e u v heq).2 huP hvP
    rcases hcover with hu | hv'
    · left
      have hp' := hp u z hz
      have he' : Classical.choose (hcolor u z hz) = e := hh u _ _ hp'.1 huE (hp'.2.1.trans hu.symm)
      have other := op874pft_other_edge u e huE
      rw [heq] at other
      have hv' : op874pft_other u e = v := by simpa [Sym2.eq_iff,huv,huv.symm] using other.symm
      simpa [he',hv'] using hp'.2.2
    · right
      have hp' := hp v z hv
      have he' : Classical.choose (hcolor v z hv) = e := hh v _ _ hp'.1 hvE (hp'.2.1.trans hv'.symm)
      have other := op874pft_other_edge v e hvE
      rw [heq] at other
      have hu' : op874pft_other v e = u := by simpa [Sym2.eq_iff,huv,huv.symm] using other.symm
      simpa [he',hu'] using hp'.2.2
