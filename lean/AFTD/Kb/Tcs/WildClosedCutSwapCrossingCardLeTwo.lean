import AFTD.Prelude
import AFTD.Kb.Tcs.WildClosedCutSwapCrossingIncident
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_closed_cut_swap_crossing_card_le_two

Topic: graphs   Node: 441448a74557

Provenance: helper lemma. Helper for the structural exchange route in the OP-306 campaign on arXiv:2610.22142. This records a cut obstruction or a sufficient test for exchanges, not a new wild-number bound.

For any proper edge coloring of a complete graph, if the image of a vertex cut U under a transposition is closed for color i, at most two ordered color-i edges cross the original cut from U to its complement.
-/

open scoped Classical
set_option maxHeartbeats 1000000

theorem wild_closed_cut_swap_crossing_card_le_two {n k : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (i : Fin k) (U : Finset (Fin n)) (a b : Fin n)
    (hclosed : w279_closed c i (U.image (Equiv.swap a b))) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun uv =>
      ∃ h : uv.1 ≠ uv.2, uv.1 ∈ U ∧ uv.2 ∉ U ∧
        c ⟨s(uv.1,uv.2),wild_kn_mem h⟩ = i)).card ≤ 2 := by
  classical
  let E := ((Finset.univ : Finset (Fin n × Fin n)).filter (fun uv =>
      ∃ h : uv.1 ≠ uv.2, uv.1 ∈ U ∧ uv.2 ∉ U ∧
        c ⟨s(uv.1,uv.2),wild_kn_mem h⟩ = i))
  let f : Fin n × Fin n → Fin 2 := fun uv => if uv.1 = a ∨ uv.2 = a then 0 else 1
  have hf : Set.InjOn f (↑E) := by
    intro x hx y hy hxy
    obtain ⟨hxne,hxU,hxnU,hxc⟩ := (Finset.mem_filter.1 hx).2
    obtain ⟨hyne,hyU,hynU,hyc⟩ := (Finset.mem_filter.1 hy).2
    have hxinc := wild_closed_cut_swap_crossing_incident c i U a b hclosed x.1 x.2 hxne hxU hxnU hxc
    have hyinc := wild_closed_cut_swap_crossing_incident c i U a b hclosed y.1 y.2 hyne hyU hynU hyc
    have common : (x.1 = a ∨ x.2 = a) ∧ (y.1 = a ∨ y.2 = a) ∨
        (x.1 = b ∨ x.2 = b) ∧ (y.1 = b ∨ y.2 = b) := by
      simp only [f] at hxy
      split_ifs at hxy with hxa hya
      · exact Or.inl ⟨hxa,hya⟩
      · norm_num at hxy
      · norm_num at hxy
      · exact Or.inr ⟨by tauto, by tauto⟩
    have hshare : ∀ z, (x.1 = z ∨ x.2 = z) → (y.1 = z ∨ y.2 = z) → x = y := by
      intro z hxz hyz
      rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
      · have hfst : x.1 = y.1 := hxz.trans hyz.symm
        have hsnd : x.2 = y.2 := wild_kn_same_color c hxne (by simpa only [← hfst] using hyne)
          (by simpa only [← hfst] using hxc.trans hyc.symm)
        exact Prod.ext hfst hsnd
      · exact False.elim (hynU (hyz.symm ▸ hxz ▸ hxU))
      · exact False.elim (hxnU (hxz.symm ▸ hyz ▸ hyU))
      · have hsnd : x.2 = y.2 := hxz.trans hyz.symm
        have hfst : x.1 = y.1 := wild_kn_same_color c (Ne.symm hxne)
          (by simpa only [← hsnd] using Ne.symm hyne)
          (by
            have hxcol := (w279_c_swap c (Ne.symm hxne)).trans hxc
            have hycol := (w279_c_swap c (Ne.symm hyne)).trans hyc
            simpa only [← hsnd] using hxcol.trans hycol.symm)
        exact Prod.ext hfst hsnd
    rcases common with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact hshare a hx hy
    · exact hshare b hx hy
  have hc := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hf
  simpa only [Finset.card_univ,Fintype.card_fin] using hc
