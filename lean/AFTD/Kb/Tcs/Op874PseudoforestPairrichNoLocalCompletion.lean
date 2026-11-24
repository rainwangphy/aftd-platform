import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges
import AFTD.Kb.Tcs.Op874pfMissing
import AFTD.Kb.Tcs.Op874PseudoforestPairrichNoPortCover

/-!
# op874_pseudoforest_pairrich_no_local_completion

Topic: graphs   Node: a69300875d0f

Provenance: helper lemma. OP-874: local-state transfer of the four-cycle parity obstruction.

For the explicit eight-vertex graph and missing-color lists there is no injective hidden-color assignment that uses every missing color and satisfies all edge-cover conditions.
-/

theorem op874_pseudoforest_pairrich_no_local_completion :
    ¬ ∃ h : Fin 8 → Fin 8 → Fin 6,
      (∀ v u w, s(v,u) ∈ op874pf_edges → s(v,w) ∈ op874pf_edges →
        h v u = h v w → u = w) ∧
      (∀ v z, z ∈ op874pf_missing v →
        ∃ w, s(v,w) ∈ op874pf_edges ∧ h v w = z) ∧
      (∀ u v z, s(u,v) ∈ op874pf_edges → z ∈ op874pf_missing u →
        z ∈ op874pf_missing v → h u v = z ∨ h v u = z) := by
  classical
  rintro ⟨h, hinj, htotal, hcover⟩
  let p (v : Fin 8) (z : Fin 6) : Fin 8 :=
    if hz : z ∈ op874pf_missing v then Classical.choose (htotal v z hz) else 0
  have hp (v : Fin 8) (z : Fin 6) (hz : z ∈ op874pf_missing v) :
      s(v,p v z) ∈ op874pf_edges ∧ h v (p v z) = z := by
    simpa only [p, dif_pos hz] using Classical.choose_spec (htotal v z hz)
  apply op874_pseudoforest_pairrich_no_port_cover
  refine ⟨p, ?_, ?_⟩
  · intro v z w hz hw hzw heq
    have hz' := (hp v z hz).2
    have hw' := (hp v w hw).2
    rw [heq] at hz'
    exact hzw (hz'.symm.trans hw')
  · intro u v z he hz hv
    rcases hcover u v z he hz hv with hu | hv'
    · left
      exact hinj u (p u z) v (hp u z hz).1 he ((hp u z hz).2.trans hu.symm)
    · right
      have he' : s(v,u) ∈ op874pf_edges := by simpa [Sym2.eq_swap] using he
      exact hinj v (p v z) u (hp v z hv).1 he' ((hp v z hv).2.trans hv'.symm)
