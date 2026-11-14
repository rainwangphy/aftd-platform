import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphLowCutContainsCycle
import AFTD.Kb.Tcs.DigraphCommonCycleCoreNeighborUnique
import AFTD.Kb.Tcs.DigraphFiniteSinkStrongSubgraph
import AFTD.Kb.Tcs.DigraphCommonCycleCoreExcludesHighDegreeVertices
import AFTD.Kb.Tcs.DigraphCommonCycleCoreOutsideInjection
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_17_shared_target_forces_two_cycles

Topic: graphs   Node: 157ab0fbc5ad

Provenance: helper lemma. Common-cycle core analysis of the oriented twenty-cut equality profile for OP-110.

The normalized oriented seventeen-vertex shared-target configuration with three designated parents contains two disjoint cycles, assuming the displayed two-cycle criterion.
-/

lemma digraph_17_shared_target_forces_two_cycles_S_ge_three
    (D : Digraph (Fin 17)) [DecidableRel D.Adj]
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v : Fin 17, 5 ≤ v.val →
      (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hlow : ∀ v : Fin 17, v.val < 5 → D.Adj v 8)
    (hout : ∀ v : Fin 17, 9 ≤ v.val → v.val < 16 → D.Adj 8 v)
    (htwo : ∀ T : Finset (Fin 17), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 17), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset (Fin 17),
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    3 ≤ (Finset.univ.filter fun r : Fin 17 => 9 ≤ r.val ∧ r.val < 16 ∧
      ∃ v : Fin 17, v.val < 5 ∧ D.Adj r v).card := by
  let R : Finset (Fin 17) := Finset.univ.filter fun v => 9 ≤ v.val ∧ v.val < 16
  let S : Finset (Fin 17) := R.filter fun r => ∃ v : Fin 17, v.val < 5 ∧ D.Adj r v
  let U := R \ S
  let P' : Finset (Fin 17) := (Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val < 8) ∪ {16}
  have hRcard : R.card = 7 := by decide
  have hP'card : P'.card = 4 := by decide
  have hSR : S ⊆ R := Finset.filter_subset _ _
  have hUcard : U.card + S.card = 7 := by
    have hh := Finset.card_sdiff_add_card_eq_card hSR
    change U.card + S.card = R.card at hh
    omega
  have hno_low (r : Fin 17) (hr : r ∈ U) :
      ∀ v : Fin 17, v.val < 5 → ¬ D.Adj r v := by
    intro v hv hadj
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrS : r ∉ S := (Finset.mem_sdiff.mp hr).2
    apply hrS
    exact Finset.mem_filter.mpr ⟨hrR, ⟨v,hv,hadj⟩⟩
  have hRbound (r : Fin 17) (hr : r ∈ U) :
      7 ≤ (R.filter fun w => D.Adj r w).card + 4 := by
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrval : 9 ≤ r.val ∧ r.val < 16 := (Finset.mem_filter.mp hrR).2
    have hn8 : ¬ D.Adj r 8 := hori 8 r (hout r hrval.1 hrval.2)
    let I := Finset.univ.filter fun w => D.Adj r w
    let K := R.filter fun w => D.Adj r w
    have hsub : I ⊆ K ∪ P' := by
      intro w hw
      have hadj : D.Adj r w := (Finset.mem_filter.mp hw).2
      by_cases hwR : 9 ≤ w.val ∧ w.val < 16
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwR⟩, hadj⟩
      · apply Finset.mem_union_right
        have hw5 : 5 ≤ w.val := by
          by_contra h
          exact hno_low r hr w (by omega) hadj
        by_cases hw16 : w.val = 16
        · have : w = 16 := Fin.ext hw16
          subst w
          exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
        · have hw8 : w.val ≠ 8 := by
            intro heq
            have : w = (8 : Fin 17) := Fin.ext heq
            subst w
            exact hn8 hadj
          have hwlt8 : w.val < 8 := by omega
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw5, hwlt8⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le K P'
    have hI : I.card = 7 := hdeg r (by omega)
    change 7 ≤ K.card + 4
    omega
  have hUbound (r : Fin 17) (hr : r ∈ U) :
      7 ≤ (U.filter fun w => D.Adj r w).card + S.card + 4 := by
    let K := R.filter fun w => D.Adj r w
    let L := U.filter fun w => D.Adj r w
    have hsub : K ⊆ L ∪ S := by
      intro w hw
      have hwR : w ∈ R := (Finset.mem_filter.mp hw).1
      have hadj : D.Adj r w := (Finset.mem_filter.mp hw).2
      by_cases hwS : w ∈ S
      · exact Finset.mem_union_right L hwS
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwR,hwS⟩,hadj⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le L S
    have h3 := hRbound r hr
    change 7 ≤ K.card + 4 at h3
    change 7 ≤ L.card + S.card + 4
    omega
  have hSeq : S = Finset.univ.filter (fun r => 9 ≤ r.val ∧ r.val < 16 ∧
      ∃ v : Fin 17, v.val < 5 ∧ D.Adj r v) := by
    ext r
    simp [S,R,Finset.mem_filter, and_assoc]
  rw [← hSeq]
  by_contra hh
  have hsle : S.card ≤ 2 := by omega
  by_cases hS : S.Nonempty
  · obtain ⟨r,hr⟩ := hS
    obtain ⟨hrR, v,hvval,hrv⟩ := Finset.mem_filter.mp hr
    have hrval : 9 ≤ r.val ∧ r.val < 16 := (Finset.mem_filter.mp hrR).2
    have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
    have hUdeg : ∀ x ∈ U, 1 ≤ (U.filter fun w => D.Adj x w).card := by
      intro x hx
      have hh := hUbound x hx
      omega
    have hloop : ∀ x, ¬ D.Adj x x := by
      intro x hx
      exact (hori x x hx) hx
    have hsuccessor : ∀ x ∈ U, ∃ w ∈ U, D.Adj x w := by
      intro x hx
      have hc := hUdeg x hx
      obtain ⟨w,hw⟩ := Finset.card_pos.mp (by omega : 0 < (U.filter fun w => D.Adj x w).card)
      exact ⟨w,(Finset.mem_filter.mp hw).1,(Finset.mem_filter.mp hw).2⟩
    obtain ⟨C,hCU,hC⟩ := digraph_low_cut_contains_cycle_outdeg_cycle (Fin 17) D hloop U hUne hsuccessor
    have hv8 : v ≠ (8 : Fin 17) := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hvr : v ≠ r := by intro h; have := congrArg Fin.val h; omega
    have h8r : (8 : Fin 17) ≠ r := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htri : digraph_directed_cycle_on D ({v,8,r} : Finset (Fin 17)) := by
      refine ⟨[v,8,r], ?_, by simp, by simp, ?_, ?_⟩
      · simp [hv8,hvr,h8r]
      · simpa [List.isChain_cons_cons] using ⟨hlow v hvval,hout r hrval.1 hrval.2⟩
      · exact ⟨v,r,by simp,by simp,hrv⟩
    have hdis : Disjoint ({v,8,r} : Finset (Fin 17)) C := by
      apply Finset.disjoint_left.mpr
      intro x hx hxc
      have hxU : x ∈ U := hCU hxc
      have hxR : x ∈ R := (Finset.mem_sdiff.mp hxU).1
      have hxval : 9 ≤ x.val ∧ x.val < 16 := (Finset.mem_filter.mp hxR).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · norm_num at hxval
      · exact (Finset.mem_sdiff.mp hxU).2 hr
    let f : Fin 2 → Finset (Fin 17) := Fin.cases {v,8,r} (fun _ => C)
    apply hno
    refine ⟨f, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact htri
      · exact hC
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | exact (hij rfl).elim | exact hdis | exact hdis.symm
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    have hRdeg : ∀ r ∈ R, 3 ≤ (R.filter fun w => D.Adj r w).card := by
      intro r hr
      have hrU : r ∈ U := by simpa [U,hS0] using hr
      have hh := hRbound r hrU
      omega
    obtain ⟨c,hc,hdis⟩ := htwo R hRne hRdeg
    apply hno
    exact ⟨c,fun i => (hc i).2,hdis⟩

theorem digraph_17_shared_target_forces_two_cycles
    (D : Digraph (Fin 17)) [DecidableRel D.Adj]
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v : Fin 17, 5 ≤ v.val →
      (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hlow : ∀ v : Fin 17, v.val < 5 → D.Adj v 8)
    (hout : ∀ v : Fin 17, 9 ≤ v.val → v.val < 16 → D.Adj 8 v)
    (hparents : ∀ v : Fin 17, 5 ≤ v.val → v.val < 8 → D.Adj v 8)
    (htwo : ∀ T : Finset (Fin 17), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 17), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    ∃ c : Fin 2 → Finset (Fin 17),
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)) := by
  classical
  by_contra hno
  have hloop : ∀ v, ¬ D.Adj v v := fun v hv => hori v v hv hv
  let R : Finset (Fin 17) := Finset.univ.filter fun v => 9 ≤ v.val ∧ v.val < 16
  let P : Finset (Fin 17) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val < 8
  let P' : Finset (Fin 17) := P ∪ {16}
  let H : Finset (Fin 17) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val ≠ 8
  let S : Finset (Fin 17) := Finset.univ.filter fun r => 9 ≤ r.val ∧ r.val < 16 ∧ ∃ v : Fin 17, v.val < 5 ∧ D.Adj r v
  have hScard : 3 ≤ S.card :=
    digraph_17_shared_target_forces_two_cycles_S_ge_three D hori hdeg hlow hout htwo hno
  have hHne : H.Nonempty := ⟨(5 : Fin 17), by decide⟩
  obtain ⟨T, hTH, hTne, hsink, hstrong⟩ := digraph_finite_sink_strong_subgraph (Fin 17) D H hHne
  have hcore_H (C : Finset (Fin 17)) (hCH : C ⊆ H) (hC : digraph_directed_cycle_on D C) : S ⊆ C := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨-, hsval, hsval2, v, hvval, hsv⟩ := hs
    by_contra hsC
    have hv8 : v ≠ (8 : Fin 17) := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hvs : v ≠ s := by intro h; have := congrArg Fin.val h; omega
    have h8s : (8 : Fin 17) ≠ s := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htri : digraph_directed_cycle_on D ({v,8,s} : Finset (Fin 17)) := by
      refine ⟨[v,8,s], ?_, by simp, by simp, ?_, ?_⟩
      · simp [hv8,hvs,h8s]
      · simpa [List.isChain_cons_cons] using ⟨hlow v hvval, hout s hsval hsval2⟩
      · exact ⟨v,s,by simp,by simp,hsv⟩
    have hdis : Disjoint ({v,8,s} : Finset (Fin 17)) C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      have hxH : x ∈ H := hCH hxC
      rw [Finset.mem_filter] at hxH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · exact hxH.2.2 rfl
      · exact hsC hxC
    let f : Fin 2 → Finset (Fin 17) := Fin.cases {v,8,s} (fun _ => C)
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
    have hHc : (Hᶜ : Finset (Fin 17)).card = 6 := by decide
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
  obtain ⟨C0, hC0T, hC0⟩ := digraph_low_cut_contains_cycle_outdeg_cycle (Fin 17) D hloop T hTne hsucc
  have hST : S ⊆ T := (hcore_H C0 (hC0T.trans hTH) hC0).trans hC0T
  have hcore_T : ∀ C ⊆ T, digraph_directed_cycle_on D C → S ⊆ C :=
    fun C hCsub hCcyc => hcore_H C (hCsub.trans hTH) hCcyc
  have hs_deg : ∀ s ∈ S, 2 ≤ (T.filter fun w => D.Adj s w).card := by
    intro s hs
    have hsT : s ∈ T := hST hs
    have hsval : 9 ≤ s.val ∧ s.val < 16 := ⟨(Finset.mem_filter.mp hs).2.1, (Finset.mem_filter.mp hs).2.2.1⟩
    have hn8 : ¬ D.Adj s 8 := hori 8 s (hout s hsval.1 hsval.2)
    let N := Finset.univ.filter fun w => D.Adj s w
    have hNcard : N.card = 7 := hdeg s (by omega)
    let L : Finset (Fin 17) := Finset.univ.filter fun w => w.val < 5
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
  have hinj := digraph_common_cycle_core_outside_injection (Fin 17) D T S S hST (subset_refl S) hloop hstrong hcore_T hs_deg
  have hneS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcover : T ⊆ R ∪ P' := by
    intro x hx
    have hxH := hTH hx
    rw [Finset.mem_filter] at hxH
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    by_cases hx8 : x.val < 8
    · right; left
      exact ⟨Finset.mem_univ x, hxH.2.1, hx8⟩
    · by_cases hx16 : x.val < 16
      · left
        have : 9 ≤ x.val := by
          have : x.val ≠ 8 := hxH.2.2
          omega
        exact ⟨Finset.mem_univ x, this, hx16⟩
      · right; right
        ext; omega
  have hP'card : P'.card + 2 ≤ 6 := by decide
  have huniq (x : Fin 17) (hx : x ∈ T) : (S.filter fun y => D.Adj x y).card ≤ 1 :=
    (digraph_common_cycle_core_neighbor_unique (Fin 17) D T S hST hloop hstrong hcore_T x hx).1
  have hdeg6 (x : Fin 17) (hxT : x ∈ T) (hxR : x ∈ R) (hxS : x ∉ S) : 6 ≤ (T.filter fun y => D.Adj x y).card := by
    have hxval : 9 ≤ x.val ∧ x.val < 16 := (Finset.mem_filter.mp hxR).2
    have hn8 : ¬ D.Adj x 8 := hori 8 x (hout x hxval.1 hxval.2)
    have hnolow : ∀ v : Fin 17, v.val < 5 → ¬ D.Adj x v := by
      intro v hv hadj
      apply hxS
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hxval.1, hxval.2, v, hv, hadj⟩
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
    digraph_common_cycle_core_excludes_high_degree_vertices (Fin 17) D T R S P' 6 hloop hneS hcover hP'card hcore_T huniq hdeg6
  have hsubP' : T \ S ⊆ P' := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxT := hx.1
    have hxS := hx.2
    have hxRP := hcover hxT
    rw [Finset.mem_union] at hxRP
    rcases hxRP with hxR | hxP'
    · exfalso
      have hxRS : x ∈ R \ S := Finset.mem_sdiff.mpr ⟨hxR, hxS⟩
      exact Finset.disjoint_left.mp hdisj_T_RS hxT hxRS
    · exact hxP'
  have hP'4 : P'.card = 4 := by decide
  have hle4 : (T \ S).card ≤ 4 := by
    have := Finset.card_le_card hsubP'
    omega
  have hSle4 : S.card ≤ 4 := le_trans hinj hle4
  let K : Finset (Fin 17) := T.filter fun v => ∀ C : Finset (Fin 17), C ⊆ T → digraph_directed_cycle_on D C → v ∈ C
  have hKT : K ⊆ T := Finset.filter_subset _ _
  have hSK : S ⊆ K := by
    intro s hs
    rw [Finset.mem_filter]
    refine ⟨hST hs, ?_⟩
    intro C hCT hC
    exact hcore_T C hCT hC hs
  have hcore_T_K : ∀ C ⊆ T, digraph_directed_cycle_on D C → K ⊆ C := by
    intro C hCT hC v hv
    rw [Finset.mem_filter] at hv
    exact hv.2 C hCT hC
  have hinj_K := digraph_common_cycle_core_outside_injection (Fin 17) D T K S hKT hSK hloop hstrong hcore_T_K hs_deg
  have h1 := Finset.card_sdiff_add_card_eq_card hKT
  have h2 := Finset.card_sdiff_add_card_eq_card hST
  have hKcard_le : K.card ≤ 4 := by omega
  have hSP : Disjoint S P := by
    rw [Finset.disjoint_left]
    intro x hxS hxP
    rw [Finset.mem_filter] at hxS hxP
    omega
  have hdisj_KP_S : Disjoint (K ∩ P) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    rw [Finset.mem_inter] at hx
    exact (Finset.disjoint_left.mp hSP) hxS hx.2
  have hsubK : (K ∩ P) ∪ S ⊆ K := by
    rw [Finset.union_subset_iff]
    exact ⟨Finset.inter_subset_left, hSK⟩
  have h5 : (K ∩ P).card + S.card ≤ K.card := by
    have := Finset.card_le_card hsubK
    rwa [Finset.card_union_of_disjoint hdisj_KP_S] at this
  have hPKle1 : (P ∩ K).card ≤ 1 := by
    have : (P ∩ K).card = (K ∩ P).card := by rw [Finset.inter_comm]
    omega
  have hno_omit : ∀ p ∈ P \ K, ∀ r ∈ R \ S, ¬ D.Adj r p := by
    intro p hpPK r hr hrp
    have hpP : p ∈ P := (Finset.mem_sdiff.mp hpPK).1
    have hpK : p ∉ K := (Finset.mem_sdiff.mp hpPK).2
    have hpval : 5 ≤ p.val ∧ p.val < 8 := (Finset.mem_filter.mp hpP).2
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrval : 9 ≤ r.val ∧ r.val < 16 := (Finset.mem_filter.mp hrR).2
    have hex_avoid : ∃ C, C ⊆ T ∧ digraph_directed_cycle_on D C ∧ p ∉ C := by
      by_cases hpT : p ∈ T
      · have : ¬ (∀ C, C ⊆ T → digraph_directed_cycle_on D C → p ∈ C) := by
          intro hall
          apply hpK
          rw [Finset.mem_filter]
          exact ⟨hpT, hall⟩
        by_contra hno_avoid
        apply this
        intro C hCT hC
        by_contra hpC
        exact hno_avoid ⟨C, hCT, hC, hpC⟩
      · exact ⟨C0, hC0T, hC0, fun hpC0 => hpT (hC0T hpC0)⟩
    obtain ⟨C, hCT, hC, hpC⟩ := hex_avoid
    have h8r : D.Adj 8 r := hout r hrval.1 hrval.2
    have hp8 : D.Adj p 8 := hparents p hpval.1 hpval.2
    have h8r_ne : (8 : Fin 17) ≠ r := by intro h; have := congrArg Fin.val h; omega
    have hrp_ne : r ≠ p := by intro h; have := congrArg Fin.val h; omega
    have hp8_ne : p ≠ (8 : Fin 17) := by intro h; have := congrArg Fin.val h; omega
    have htri : digraph_directed_cycle_on D ({8, r, p} : Finset (Fin 17)) := by
      refine ⟨[8, r, p], ?_, by simp, by simp, ?_, ?_⟩
      · simp [h8r_ne, hrp_ne, hp8_ne.symm]
      · simpa [List.isChain_cons_cons] using ⟨h8r, hrp⟩
      · exact ⟨8, p, by simp, by simp, hp8⟩
    have hdis : Disjoint ({8, r, p} : Finset (Fin 17)) C := by
      rw [Finset.disjoint_left]
      intro x hx hxC
      have hxT : x ∈ T := hCT hxC
      have hxH : x ∈ H := hTH hxT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx8 | hxr | hxp
      · subst hx8
        rw [Finset.mem_filter] at hxH
        exact hxH.2.2 rfl
      · have hrT : r ∈ T := hxr ▸ hxT
        exact Finset.disjoint_left.mp hdisj_T_RS hrT hr
      · have hpC' : p ∈ C := hxp ▸ hxC
        exact hpC hpC'
    let f : Fin 2 → Finset (Fin 17) := Fin.cases {8, r, p} (fun _ => C)
    apply hno
    refine ⟨f, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact htri
      · exact hC
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | exact (hij rfl).elim | exact hdis | exact hdis.symm
  have hUdeg : ∀ r ∈ R \ S, 1 ≤ ((R \ S).filter fun w => D.Adj r w).card := by
    intro r hr
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrS : r ∉ S := (Finset.mem_sdiff.mp hr).2
    have hrval : 9 ≤ r.val ∧ r.val < 16 := (Finset.mem_filter.mp hrR).2
    have hn8 : ¬ D.Adj r 8 := hori 8 r (hout r hrval.1 hrval.2)
    have hnolow : ∀ v : Fin 17, v.val < 5 → ¬ D.Adj r v := by
      intro v hv hadj
      apply hrS
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ r, hrval.1, hrval.2, v, hv, hadj⟩
    let N := Finset.univ.filter fun w => D.Adj r w
    have hNcard : N.card = 7 := hdeg r (by omega)
    let U := R \ S
    let A := U.filter fun w => D.Adj r w
    let B := S ∪ {16} ∪ (P ∩ K)
    have hsub : N ⊆ A ∪ B := by
      intro w hw
      have hadj : D.Adj r w := (Finset.mem_filter.mp hw).2
      by_cases hwU : w ∈ U
      · exact Finset.mem_union_left B (Finset.mem_filter.mpr ⟨hwU, hadj⟩)
      · apply Finset.mem_union_right
        have hw5 : 5 ≤ w.val := by
          by_contra h
          exact hnolow w (by omega) hadj
        have hwne8 : w ≠ (8 : Fin 17) := by
          intro heq; subst w; exact hn8 hadj
        by_cases hw16 : w.val = 16
        · have : w = 16 := Fin.ext hw16
          subst w
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
        · by_cases hwR : 9 ≤ w.val ∧ w.val < 16
          · have hwR_in : w ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwR⟩
            have hwS : w ∈ S := by
              by_contra hnotS
              exact hwU (Finset.mem_sdiff.mpr ⟨hwR_in, hnotS⟩)
            exact Finset.mem_union_left _ (Finset.mem_union_left _ hwS)
          · have hwP : w ∈ P := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ w, hw5, ?_⟩
              have : w.val ≠ 8 := fun h => hwne8 (Fin.ext h)
              omega
            have hwK : w ∈ K := by
              by_contra hnotK
              have hwPK : w ∈ P \ K := Finset.mem_sdiff.mpr ⟨hwP, hnotK⟩
              exact hno_omit w hwPK r hr hadj
            exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwP, hwK⟩)
    have h1 := Finset.card_le_card hsub
    have hl1 : B.card ≤ (S ∪ {(16 : Fin 17)}).card + (P ∩ K).card :=
      Finset.card_union_le _ _
    have hl2 : (S ∪ {(16 : Fin 17)}).card ≤ S.card + 1 := by
      have := Finset.card_union_le S {(16 : Fin 17)}
      simp only [Finset.card_singleton] at this
      exact this
    have h2 : B.card ≤ S.card + 2 := by omega
    have h3 := Finset.card_union_le A B
    change 1 ≤ A.card
    omega
  have hRcard : R.card = 7 := by decide
  have hSR : S ⊆ R := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ x, hx.2.1, hx.2.2.1⟩
  have hUcard : (R \ S).card + S.card = 7 := by
    have hh := Finset.card_sdiff_add_card_eq_card hSR
    omega
  have hUne : (R \ S).Nonempty := Finset.card_pos.mp (by omega)
  have hsucc_U : ∀ x ∈ R \ S, ∃ w ∈ R \ S, D.Adj x w := by
    intro x hx
    have hc := hUdeg x hx
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ((R \ S).filter fun w => D.Adj x w).card)
    exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  obtain ⟨CRS, hCRSU, hCRS⟩ := digraph_low_cut_contains_cycle_outdeg_cycle (Fin 17) D hloop (R \ S) hUne hsucc_U
  have hdis_T_CRS : Disjoint C0 CRS := by
    rw [Finset.disjoint_left]
    intro x hxC0 hxCRS
    have hxT : x ∈ T := hC0T hxC0
    have hxRS : x ∈ R \ S := hCRSU hxCRS
    exact Finset.disjoint_left.mp hdisj_T_RS hxT hxRS
  let f : Fin 2 → Finset (Fin 17) := Fin.cases C0 (fun _ => CRS)
  apply hno
  refine ⟨f, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hC0
    · exact hCRS
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | exact hdis_T_CRS | exact hdis_T_CRS.symm
