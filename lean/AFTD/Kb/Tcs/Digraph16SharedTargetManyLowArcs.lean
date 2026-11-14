import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphLowCutContainsCycle

/-!
# digraph_16_shared_target_many_low_arcs

Topic: graphs   Node: d81226b2ea27

Provenance: helper lemma. Analysis of the normalized first equality-profile size for OP-110.

In the displayed oriented sixteen-vertex configuration with no two disjoint cycles, at least four outneighbors of the common target point to the five low vertices, assuming the displayed two-cycle criterion.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem digraph_16_shared_target_many_low_arcs
    (D : Digraph (Fin 16)) [DecidableRel D.Adj]
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hdeg : ∀ v : Fin 16, 9 ≤ v.val →
      (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hlow : ∀ v : Fin 16, v.val < 5 → D.Adj v 8)
    (hout : ∀ v : Fin 16, 9 ≤ v.val → D.Adj 8 v)
    (htwo : ∀ T : Finset (Fin 16), T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset (Fin 16), (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset (Fin 16),
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    4 ≤ (Finset.univ.filter fun r : Fin 16 => 9 ≤ r.val ∧
      ∃ v : Fin 16, v.val < 5 ∧ D.Adj r v).card := by
  classical
  let R : Finset (Fin 16) := Finset.univ.filter fun v => 9 ≤ v.val
  let S : Finset (Fin 16) := R.filter fun r => ∃ v : Fin 16, v.val < 5 ∧ D.Adj r v
  let U := R \ S
  let P : Finset (Fin 16) := Finset.univ.filter fun v => 5 ≤ v.val ∧ v.val < 8
  have hRcard : R.card = 7 := by decide
  have hPcard : P.card = 3 := by decide
  have hSR : S ⊆ R := Finset.filter_subset _ _
  have hUcard : U.card + S.card = 7 := by
    have hh := Finset.card_sdiff_add_card_eq_card hSR
    change U.card + S.card = R.card at hh
    omega
  have hno_low (r : Fin 16) (hr : r ∈ U) :
      ∀ v : Fin 16, v.val < 5 → ¬ D.Adj r v := by
    intro v hv hadj
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrS : r ∉ S := (Finset.mem_sdiff.mp hr).2
    apply hrS
    exact Finset.mem_filter.mpr ⟨hrR, ⟨v,hv,hadj⟩⟩
  have hRbound (r : Fin 16) (hr : r ∈ U) :
      7 ≤ (R.filter fun w => D.Adj r w).card + 3 := by
    have hrR : r ∈ R := (Finset.mem_sdiff.mp hr).1
    have hrval : 9 ≤ r.val := (Finset.mem_filter.mp hrR).2
    have hn8 : ¬ D.Adj r 8 := hori 8 r (hout r hrval)
    let I := Finset.univ.filter fun w => D.Adj r w
    let K := R.filter fun w => D.Adj r w
    have hsub : I ⊆ K ∪ P := by
      intro w hw
      have hadj : D.Adj r w := (Finset.mem_filter.mp hw).2
      by_cases hw9 : 9 ≤ w.val
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw9⟩, hadj⟩
      · have hw5 : 5 ≤ w.val := by
          by_contra h
          exact hno_low r hr w (by omega) hadj
        have hw8 : w.val < 8 := by
          by_contra h
          have heq : w = (8 : Fin 16) := Fin.ext (by omega)
          subst w
          exact hn8 hadj
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw5,hw8⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le K P
    have hI : I.card = 7 := hdeg r hrval
    change 7 ≤ K.card + 3
    omega
  have hUbound (r : Fin 16) (hr : r ∈ U) :
      7 ≤ (U.filter fun w => D.Adj r w).card + S.card + 3 := by
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
    change 7 ≤ K.card + 3 at h3
    change 7 ≤ L.card + S.card + 3
    omega
  have hSeq : S = Finset.univ.filter (fun r => 9 ≤ r.val ∧
      ∃ v : Fin 16, v.val < 5 ∧ D.Adj r v) := by
    ext r
    simp [S,R,Finset.mem_filter]
  rw [← hSeq]
  by_contra hh
  have hsle : S.card ≤ 3 := by omega
  by_cases hS : S.Nonempty
  · obtain ⟨r,hr⟩ := hS
    obtain ⟨hrR, v,hvval,hrv⟩ := Finset.mem_filter.mp hr
    have hrval : 9 ≤ r.val := (Finset.mem_filter.mp hrR).2
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
    obtain ⟨C,hCU,hC⟩ := digraph_low_cut_contains_cycle_outdeg_cycle (Fin 16) D hloop U hUne hsuccessor
    have hv8 : v ≠ (8 : Fin 16) := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have hvr : v ≠ r := by intro h; have := congrArg Fin.val h; omega
    have h8r : (8 : Fin 16) ≠ r := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htri : digraph_directed_cycle_on D ({v,8,r} : Finset (Fin 16)) := by
      refine ⟨[v,8,r], ?_, by simp, by simp, ?_, ?_⟩
      · simp [hv8,hvr,h8r]
      · simpa [List.isChain_cons_cons] using ⟨hlow v hvval,hout r hrval⟩
      · exact ⟨v,r,by simp,by simp,hrv⟩
    have hdis : Disjoint ({v,8,r} : Finset (Fin 16)) C := by
      apply Finset.disjoint_left.mpr
      intro x hx hxc
      have hxU : x ∈ U := hCU hxc
      have hxR : x ∈ R := (Finset.mem_sdiff.mp hxU).1
      have hxval : 9 ≤ x.val := (Finset.mem_filter.mp hxR).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · omega
      · norm_num at hxval
      · exact (Finset.mem_sdiff.mp hxU).2 hr
    let f : Fin 2 → Finset (Fin 16) := Fin.cases {v,8,r} (fun _ => C)
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
