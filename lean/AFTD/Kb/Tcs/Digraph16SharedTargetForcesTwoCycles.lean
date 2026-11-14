import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.Digraph16SharedTargetManyLowArcs
import AFTD.Kb.Tcs.DigraphCommonCycleCoreNeighborUnique
import AFTD.Kb.Tcs.DigraphLowCutContainsCycle
import AFTD.Kb.Tcs.DigraphFiniteSinkStrongSubgraph
import AFTD.Kb.Tcs.DigraphCommonCycleCoreExcludesHighDegreeVertices
import AFTD.Kb.Tcs.DigraphCommonCycleCoreOutsideInjection
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_16_shared_target_forces_two_cycles

Topic: graphs   Node: c688c49630f6

Provenance: helper lemma. Common-cycle core route for the first remaining oriented twenty-cut equality-profile size in OP-110.

The normalized oriented sixteen-vertex shared-target configuration contains two disjoint cycles, assuming the displayed two-cycle criterion.
-/

theorem digraph_16_shared_target_forces_two_cycles
    (D : Digraph (Fin 16)) [DecidableRel D.Adj]
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v : Fin 16, 5 ≤ v.val →
      (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hlow : ∀ v : Fin 16, v.val < 5 → D.Adj v 8)
    (hout : ∀ v : Fin 16, 9 ≤ v.val → D.Adj 8 v)
    (htwo : ∀ T : Finset (Fin 16), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 16), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    ∃ c : Fin 2 → Finset (Fin 16),
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)) := by
  classical
  by_contra hno
  have hloop : ∀ v, ¬ D.Adj v v := fun v hv => hori v v hv hv
  let R : Finset (Fin 16) := Finset.univ.filter fun v => 9 ≤ v.val
  let P : Finset (Fin 16) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val < 8
  let H : Finset (Fin 16) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val ≠ 8
  let S : Finset (Fin 16) := Finset.univ.filter fun r => 9 ≤ r.val ∧ ∃ v : Fin 16, v.val < 5 ∧ D.Adj r v
  have hScard : 4 ≤ S.card :=
    digraph_16_shared_target_many_low_arcs D hori (fun v hv => hdeg v (by omega)) hlow hout htwo hno
  have hHne : H.Nonempty := ⟨(5 : Fin 16), by decide⟩
  obtain ⟨T, hTH, hTne, hsink, hstrong⟩ := digraph_finite_sink_strong_subgraph (Fin 16) D H hHne
  have hcore_H (C : Finset (Fin 16)) (hCH : C ⊆ H) (hC : digraph_directed_cycle_on D C) : S ⊆ C := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨-, hsval, v, hvval, hsv⟩ := hs
    by_contra hsC
    have hv8 : v ≠ (8 : Fin 16) := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hvs : v ≠ s := by intro h; have := congrArg Fin.val h; omega
    have h8s : (8 : Fin 16) ≠ s := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htri : digraph_directed_cycle_on D ({v,8,s} : Finset (Fin 16)) := by
      refine ⟨[v,8,s], ?_, by simp, by simp, ?_, ?_⟩
      · simp [hv8,hvs,h8s]
      · simpa [List.isChain_cons_cons] using ⟨hlow v hvval, hout s hsval⟩
      · exact ⟨v,s,by simp,by simp,hsv⟩
    have hdis : Disjoint ({v,8,s} : Finset (Fin 16)) C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      have hxH : x ∈ H := hCH hxC
      rw [Finset.mem_filter] at hxH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · exact hxH.2.2 rfl
      · exact hsC hxC
    let f : Fin 2 → Finset (Fin 16) := Fin.cases {v,8,s} (fun _ => C)
    apply hno
    refine ⟨f, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact htri
      · exact hC
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | exact (hij rfl).elim | exact hdis | exact hdis.symm
  have hsucc : ∀ v ∈ T, ∃ w ∈ T, D.Adj v w := by
    intro v hv
    have hvH : v ∈ H := hTH hv
    rw [Finset.mem_filter] at hvH
    let N := Finset.univ.filter fun w => D.Adj v w
    have h7 : N.card = 7 := hdeg v hvH.2.1
    have hHc : (Hᶜ : Finset (Fin 16)).card = 6 := by decide
    have hNne : ¬ (N ⊆ Hᶜ) := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    rw [Finset.not_subset] at hNne
    obtain ⟨w, hwN, hwHc⟩ := hNne
    rw [Finset.mem_compl] at hwHc
    have hwH : w ∈ H := Classical.not_not.mp hwHc
    rw [Finset.mem_filter] at hwN
    exact ⟨w, hsink v hv w hwH hwN.2, hwN.2⟩
  obtain ⟨C, hCT, hC⟩ := digraph_low_cut_contains_cycle_outdeg_cycle (Fin 16) D hloop T hTne hsucc
  have hST : S ⊆ T := (hcore_H C (hCT.trans hTH) hC).trans hCT
  have hcore_T : ∀ C ⊆ T, digraph_directed_cycle_on D C → S ⊆ C :=
    fun C hCsub hCcyc => hcore_H C (hCsub.trans hTH) hCcyc
  have hs_deg : ∀ s ∈ S, 2 ≤ (T.filter fun w => D.Adj s w).card := by
    intro s hs
    have hsT : s ∈ T := hST hs
    have hsval : 9 ≤ s.val := (Finset.mem_filter.mp hs).2.1
    have hn8 : ¬ D.Adj s 8 := hori 8 s (hout s hsval)
    let N := Finset.univ.filter fun w => D.Adj s w
    have hNcard : N.card = 7 := hdeg s (by omega)
    let L : Finset (Fin 16) := Finset.univ.filter fun w => w.val < 5
    have hLcard : L.card = 5 := by decide
    let Nc := Hᶜ.filter fun w => D.Adj s w
    have hNcsub : Nc ⊆ L := by
      intro w hw
      have hadj : D.Adj s w := (Finset.mem_filter.mp hw).2
      have hnotH : w ∉ H := (Finset.mem_compl.mp (Finset.mem_filter.mp hw).1)
      have hwlow : w.val < 5 := by
        by_contra hcon
        have h5 : 5 ≤ w.val := by omega
        have hne8 : w.val ≠ 8 := by
          intro heq
          have : w = 8 := Fin.ext heq
          subst w
          exact hn8 hadj
        apply hnotH
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, h5, hne8⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwlow⟩
    have hNccard : Nc.card ≤ 5 := by
      have := Finset.card_le_card hNcsub
      omega
    let Nh := H.filter fun w => D.Adj s w
    have hNh_eq : Nh = T.filter fun w => D.Adj s w := by
      ext w
      simp only [Finset.mem_filter, Nh]
      constructor
      · rintro ⟨hwH, hadj⟩
        exact ⟨hsink s hsT w hwH hadj, hadj⟩
      · rintro ⟨hwT, hadj⟩
        exact ⟨hTH hwT, hadj⟩
    have hdecomp : N = Nh ∪ Nc := by
      ext w
      simp only [N, Nh, Nc, Finset.mem_filter, Finset.mem_union, Finset.mem_compl, Finset.mem_univ, true_and]
      by_cases hw : w ∈ H <;> simp [hw]
    have hdisj : Disjoint Nh Nc := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have : x ∉ H := Finset.mem_compl.mp (Finset.mem_filter.mp hx2).1
      exact this (Finset.mem_filter.mp hx1).1
    have hsum : N.card = Nh.card + Nc.card := by
      rw [hdecomp, Finset.card_union_of_disjoint hdisj]
    rw [hNh_eq] at hsum
    omega
  have hinj := digraph_common_cycle_core_outside_injection (Fin 16) D T S S hST (subset_refl S) hloop hstrong hcore_T hs_deg
  have hdiff4 : 4 ≤ (T \ S).card := le_trans hScard hinj
  have hneS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcover : T ⊆ R ∪ P := by
    intro x hx
    have hxH := hTH hx
    rw [Finset.mem_filter] at hxH
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hx8 : x.val < 8
    · right
      exact ⟨Finset.mem_univ x, hxH.2.1, hx8⟩
    · left
      have : 9 ≤ x.val := by
        have : x.val ≠ 8 := hxH.2.2
        omega
      exact ⟨Finset.mem_univ x, this⟩
  have hPcard : P.card + 2 ≤ 5 := by decide
  have huniq (x : Fin 16) (hx : x ∈ T) : (S.filter fun y => D.Adj x y).card ≤ 1 :=
    (digraph_common_cycle_core_neighbor_unique (Fin 16) D T S hST hloop hstrong hcore_T x hx).1
  have hdeg5 (x : Fin 16) (hxT : x ∈ T) (hxR : x ∈ R) (hxS : x ∉ S) : 5 ≤ (T.filter fun y => D.Adj x y).card := by
    have hxval : 9 ≤ x.val := (Finset.mem_filter.mp hxR).2
    have hn8 : ¬ D.Adj x 8 := hori 8 x (hout x hxval)
    have hnolow : ∀ v : Fin 16, v.val < 5 → ¬ D.Adj x v := by
      intro v hv hadj
      apply hxS
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hxval, v, hv, hadj⟩
    let N := Finset.univ.filter fun w => D.Adj x w
    have hNcard : N.card = 7 := hdeg x (by omega)
    have hsubH : N ⊆ H := by
      intro w hw
      rw [Finset.mem_filter] at hw
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ w, ?_, ?_⟩
      · by_contra hlt
        have : w.val < 5 := by omega
        exact hnolow w this hw.2
      · intro heq
        have : w = 8 := Fin.ext heq
        subst w
        exact hn8 hw.2
    have hsubT : N ⊆ T.filter fun y => D.Adj x y := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hwH := hsubH (Finset.mem_filter.mpr hw)
      exact Finset.mem_filter.mpr ⟨hsink x hxT w hwH hw.2, hw.2⟩
    have := Finset.card_le_card hsubT
    omega
  have hdisj_T_RS : Disjoint T (R \ S) :=
    digraph_common_cycle_core_excludes_high_degree_vertices (Fin 16) D T R S P 5 hloop hneS hcover hPcard hcore_T huniq hdeg5
  have hsubP : T \ S ⊆ P := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxT := hx.1
    have hxS := hx.2
    have hxRP := hcover hxT
    rw [Finset.mem_union] at hxRP
    rcases hxRP with hxR | hxP
    · exfalso
      have hxRS : x ∈ R \ S := Finset.mem_sdiff.mpr ⟨hxR, hxS⟩
      exact Finset.disjoint_left.mp hdisj_T_RS hxT hxRS
    · exact hxP
  have hP3 : P.card = 3 := by decide
  have hle3 : (T \ S).card ≤ 3 := by
    have := Finset.card_le_card hsubP
    omega
  omega
