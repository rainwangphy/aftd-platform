import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphLowCutContainsCycle

/-!
# digraph_common_cycle_core_excludes_high_degree_vertices

Topic: graphs   Node: 26d857ce27a2

Provenance: helper lemma. Common-cycle core counting for the oriented twenty-cut profile.

Suppose a finite vertex set T is covered by R and P, P has at most k minus two vertices, every directed cycle in T contains a nonempty set S, every vertex of T has at most one outneighbor in S, and every vertex of T in R outside S has at least k outneighbors in T. Then T is disjoint from R outside S.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem digraph_common_cycle_core_excludes_high_degree_vertices
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (T R S P : Finset α) (k : ℕ) (hloop : ∀ x, ¬ D.Adj x x)
    (hne : S.Nonempty) (hcover : T ⊆ R ∪ P) (hP : P.card + 2 ≤ k)
    (hcore : ∀ C : Finset α, C ⊆ T → digraph_directed_cycle_on D C → S ⊆ C)
    (huniq : ∀ x ∈ T, (S.filter fun y => D.Adj x y).card ≤ 1)
    (hdeg : ∀ x ∈ T, x ∈ R → x ∉ S → k ≤ (T.filter fun y => D.Adj x y).card) :
    Disjoint T (R \ S) := by
  classical
  let X := T ∩ (R \ S)
  have hout : ∀ x ∈ X, 1 ≤ (X.filter fun y => D.Adj x y).card := by
    intro x hx
    have hxT : x ∈ T := (Finset.mem_inter.mp hx).1
    have hxR : x ∈ R := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
    have hxS : x ∉ S := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).2
    let I := T.filter fun y => D.Adj x y
    let A := X.filter fun y => D.Adj x y
    let B := S.filter fun y => D.Adj x y
    have hsub : I ⊆ (A ∪ B) ∪ P := by
      intro y hy
      have hyT := (Finset.mem_filter.mp hy).1
      have hyD := (Finset.mem_filter.mp hy).2
      have hyRP := hcover hyT
      by_cases hyS : y ∈ S
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hyS,hyD⟩
      · rcases Finset.mem_union.mp hyRP with hyR | hyP
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hyT,Finset.mem_sdiff.mpr ⟨hyR,hyS⟩⟩,hyD⟩
        · exact Finset.mem_union_right _ hyP
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (A ∪ B) P
    have h3 := Finset.card_union_le A B
    have h4 : B.card ≤ 1 := huniq x hxT
    have h5 : k ≤ I.card := hdeg x hxT hxR hxS
    change 1 ≤ A.card
    omega
  have hX : X = ∅ := by
    by_contra hh
    have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hh
    have hsuccessor : ∀ x ∈ X, ∃ y ∈ X, D.Adj x y := by
      intro x hx
      obtain ⟨y,hy⟩ := Finset.card_pos.mp (by have := hout x hx; omega :
        0 < (X.filter fun y => D.Adj x y).card)
      exact ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩
    obtain ⟨C,hCX,hcyc⟩ := digraph_low_cut_contains_cycle_outdeg_cycle α D hloop X hXne hsuccessor
    have hCT : C ⊆ T := by
      intro x hx
      exact (Finset.mem_inter.mp (hCX hx)).1
    have hSC := hcore C hCT hcyc
    obtain ⟨s,hs⟩ := hne
    have hsX := hCX (hSC hs)
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hsX).2).2 hs
  apply Finset.disjoint_left.mpr
  intro x hxT hxRS
  have hx : x ∈ X := Finset.mem_inter.mpr ⟨hxT,hxRS⟩
  rw [hX] at hx
  simpa using hx
