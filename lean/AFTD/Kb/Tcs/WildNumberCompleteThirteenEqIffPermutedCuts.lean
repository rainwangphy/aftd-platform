import AFTD.Prelude
import AFTD.Kb.Tcs.WildCompleteThirteenPartitionTemplate
import AFTD.Kb.Tcs.WildNoClosedUnionOfBlocks
import AFTD.Kb.Tcs.WildNumberCompleteOddEqIffOptimalPartition
import AFTD.Kb.Tcs.WildNumberCompleteGraphLargeEq
import AFTD.Kb.Tcs.WildCompleteThirteenOneSwapRepairObstruction
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq

/-!
# wild_number_complete_thirteen_eq_iff_permuted_cuts

Topic: graphs   Node: 129e3c01963c

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

For every proper 13-coloring of K_13, its wild number is nine if and only if some permutation of the canonical 3+3+3+4 vertex partition has none of the seven cuts (four blocks and three pairs of triples) closed for any color.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_number_complete_thirteen_eq_iff_permuted_cuts
    (c : (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13)) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin 13)) c = 9 ↔
      ∃ σ : Equiv.Perm (Fin 13), ∀ (j : Fin 7) (i : Fin 13),
        ¬w279_closed c i ((wsc_repair_cuts wsc_repair_blocks j).image σ) := by
  classical
  have hk := complete_graph_odd_line_graph_chromatic_number_eq 13 (by norm_num) (by decide)
  constructor
  · intro h
    have heq : simple_graph_wild_number (⊤ : SimpleGraph (Fin 13)) c = 4*((13+1)/2)/3 := by simpa using h
    obtain ⟨p,r,hr,hmin,hcut⟩ := (wild_number_complete_odd_eq_iff_optimal_partition (by norm_num) (by decide) hk c).1 heq
    obtain ⟨σ,β,hσ⟩ := wild_complete_thirteen_partition_template p hmin
    refine ⟨σ,?_⟩
    intro j i hclosed
    obtain ⟨m,hm⟩ := w279_missing_vertex_equiv 13 13 (by norm_num) (by decide) hk c
    obtain ⟨e,he⟩ := wsc_color_used (n:=13) (by norm_num) c m hm i
    have hcard : ∀ j : Fin 7, 1 ≤ (wsc_repair_cuts wsc_repair_blocks j).card ∧
        (wsc_repair_cuts wsc_repair_blocks j).card ≤ 6 := by decide +kernel
    have hown : ∀ (j : Fin 7) (u v : Fin 13), u ∈ wsc_repair_cuts wsc_repair_blocks j →
        wsc_repair_owner u = wsc_repair_owner v → v ∈ wsc_repair_cuts wsc_repair_blocks j := by decide +kernel
    let U := (wsc_repair_cuts wsc_repair_blocks j).image σ
    have hcU : U.card = (wsc_repair_cuts wsc_repair_blocks j).card :=
      Finset.card_image_of_injective _ σ.injective
    have hU : U.Nonempty := Finset.card_pos.1 (by have := (hcard j).1; omega)
    have hproper : U ≠ Finset.univ := by
      intro hh
      have hc13 : U.card = 13 := by rw [hh]; simp
      have := (hcard j).2
      omega
    have hsat : ∀ u ∈ U, ∀ v, p v = p u → v ∈ U := by
      intro u hu v hpv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
      have hvown : wsc_repair_owner (σ.symm v) = wsc_repair_owner x := by
        rw [← hσ (σ.symm v),σ.apply_symm_apply, hpv,hσ x]
      refine Finset.mem_image.2 ⟨σ.symm v, hown j x (σ.symm v) hx hvown.symm, σ.apply_symm_apply v⟩
    have hncl := wild_no_closed_union_of_blocks c p hcut e U hU hproper hsat
    exact hncl (by simpa only [he] using hclosed)
  · rintro ⟨σ,hσ⟩
    apply le_antisymm
    · let p : Fin 13 → Fin 4 := fun v => wsc_repair_owner (σ.symm v)
      let r0 (t : Fin 4) : Fin 13 := ⟨3*t.val,by have := t.isLt; omega⟩
      let r : Fin 4 → Fin 13 := fun t => σ (r0 t)
      have hroot : ∀ t, wsc_repair_owner (r0 t) = t := by decide +kernel
      have hr : ∀ t, p (r t) = t := by intro t; simpa only [p,r,Equiv.symm_apply_apply] using hroot t
      have hshape : ∀ S : Finset (Fin 4), S.Nonempty → S ≠ Finset.univ →
          ∃ j : Fin 7, (∀ v : Fin 13, wsc_repair_owner v ∈ S ↔ v ∈ wsc_repair_cuts wsc_repair_blocks j) ∨
            (∀ v : Fin 13, wsc_repair_owner v ∈ S ↔ v ∉ wsc_repair_cuts wsc_repair_blocks j) := by decide +kernel
      have hcut : ∀ (e : (⊤ : SimpleGraph (Fin 13)).edgeSet) (S : Finset (Fin 4)),
          S.Nonempty → S ≠ Finset.univ →
          ∃ (u v : Fin 13) (huv : u ≠ v), p u ∈ S ∧ p v ∉ S ∧ c ⟨s(u,v),wild_kn_mem huv⟩ = c e := by
        intro e S hS hproper
        by_contra! hno
        obtain ⟨j,hj | hj⟩ := hshape S hS hproper
        · apply hσ j (c e)
          intro u hu v huv hc
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
          by_contra hv
          have hxS : p (σ x) ∈ S := by simpa only [p,Equiv.symm_apply_apply] using (hj x).2 hx
          have hvS : p v ∉ S := by
            intro hh
            have hvD := (hj (σ.symm v)).1 hh
            exact hv (Finset.mem_image.2 ⟨σ.symm v,hvD,σ.apply_symm_apply v⟩)
          exact hno (σ x) v huv hxS hvS hc
        · apply hσ j (c e)
          intro u hu v huv hc
          obtain ⟨x,hx,rfl⟩ := Finset.mem_image.1 hu
          by_contra hv
          have hxS : p (σ x) ∉ S := by
            intro hh
            have hh' : wsc_repair_owner x ∈ S := by simpa only [p,Equiv.symm_apply_apply] using hh
            exact (hj x).1 hh' hx
          have hvS : p v ∈ S := by
            apply (hj (σ.symm v)).2
            intro hvD
            exact hv (Finset.mem_image.2 ⟨σ.symm v,hvD,σ.apply_symm_apply v⟩)
          exact hno v (σ x) (Ne.symm huv) hvS hxS ((w279_c_swap c (Ne.symm huv)).trans hc)
      have hu := simple_graph_wild_number_le_of_block_cut_condition (n:=13) (q:=4) (by norm_num) c p r hr hcut
      norm_num at hu
      exact hu
    · have hl := wild_number_complete_graph_min_proper_coloring_ge 13 13 (by norm_num) hk c
      norm_num at hl
      exact hl
