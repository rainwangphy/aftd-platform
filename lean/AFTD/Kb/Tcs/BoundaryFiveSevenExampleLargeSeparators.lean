import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveSevenExampleEdgeEssential

/-!
# boundary_five_seven_example_large_separators

Topic: graphs   Node: ab980a557a93

Provenance: helper lemma. OP-1957: size-(5,7) obstruction; experiment 37142.

Every vertex separator of the explicitly defined 28-vertex example separating two nonempty anticomplete parts has at least 14 vertices.
-/

open Classical

private def boundary_five_seven_example_large_separators_A' : Finset (Fin 28) := {1, 2, 3, 4}
private def boundary_five_seven_example_large_separators_B : Finset (Fin 28) := {5, 6, 7, 8, 9, 10, 11, 12, 13}
private def boundary_five_seven_example_large_separators_B' : Finset (Fin 28) := {6, 7, 8, 9, 10, 11, 12, 13}
private def boundary_five_seven_example_large_separators_A : Finset (Fin 28) := {0, 1, 2, 3, 4}
private def boundary_five_seven_example_large_separators_C : Finset (Fin 28) := {14, 15, 16, 17, 18, 19, 20}
private def boundary_five_seven_example_large_separators_C' : Finset (Fin 28) := {17, 18, 19, 20}
private def boundary_five_seven_example_large_separators_D : Finset (Fin 28) := {21, 22, 23, 24, 25, 26, 27}
private def boundary_five_seven_example_large_separators_T : Finset (Fin 28) := {14, 15, 16}
private def boundary_five_seven_example_large_separators_V_rem : Finset (Fin 28) := {0, 5, 14, 15, 16, 17, 18, 19, 20}
private def boundary_five_seven_example_large_separators_nn0 : Finset (Fin 28) := {5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16}
private def boundary_five_seven_example_large_separators_nn5 : Finset (Fin 28) := {0, 1, 2, 3, 4, 14, 15, 16}
private def boundary_five_seven_example_large_separators_nn (v : Fin 28) : Finset (Fin 28) :=
  Finset.univ.filter (fun u => u ≠ v ∧ ¬ in1122_fiveseven_graph.Adj u v)

private theorem boundary_five_seven_example_large_separators_A'_adj :
  ∀ u ∈ boundary_five_seven_example_large_separators_A', ∀ w : Fin 28,
    w ∉ boundary_five_seven_example_large_separators_B → w ≠ u → in1122_fiveseven_graph.Adj u w := by decide

private theorem boundary_five_seven_example_large_separators_B'_adj :
  ∀ b ∈ boundary_five_seven_example_large_separators_B', ∀ v : Fin 28,
    v ∉ boundary_five_seven_example_large_separators_A → v ≠ b → in1122_fiveseven_graph.Adj b v := by decide

private theorem boundary_five_seven_example_large_separators_D_adj :
  ∀ d ∈ boundary_five_seven_example_large_separators_D, ∀ v : Fin 28,
    v ∉ boundary_five_seven_example_large_separators_C → v ≠ d → in1122_fiveseven_graph.Adj d v := by decide

private theorem boundary_five_seven_example_large_separators_C'_adj :
  ∀ c ∈ boundary_five_seven_example_large_separators_C', ∀ v : Fin 28,
    v ∉ boundary_five_seven_example_large_separators_D → v ≠ c → in1122_fiveseven_graph.Adj c v := by decide

private theorem boundary_five_seven_example_large_separators_nn0_prop :
  ∀ v : Fin 28, v ≠ 0 → ¬ in1122_fiveseven_graph.Adj 0 v → v ∈ boundary_five_seven_example_large_separators_nn0 := by decide

private theorem boundary_five_seven_example_large_separators_nn5_prop :
  ∀ v : Fin 28, v ≠ 5 → ¬ in1122_fiveseven_graph.Adj 5 v → v ∈ boundary_five_seven_example_large_separators_nn5 := by decide

private theorem boundary_five_seven_example_large_separators_T_nn :
  ∀ w ∈ boundary_five_seven_example_large_separators_T,
    (boundary_five_seven_example_large_separators_nn w).card ≤ 11 := by decide

private theorem boundary_five_seven_example_large_separators_univ_cover :
  boundary_five_seven_example_large_separators_A' ∪
  boundary_five_seven_example_large_separators_B' ∪
  boundary_five_seven_example_large_separators_D ∪
  boundary_five_seven_example_large_separators_V_rem = Finset.univ := by decide

private theorem boundary_five_seven_example_large_separators_B_sdiff_B' :
  boundary_five_seven_example_large_separators_B \ boundary_five_seven_example_large_separators_B' = {5} := by decide

private theorem boundary_five_seven_example_large_separators_A_sdiff_A' :
  boundary_five_seven_example_large_separators_A \ boundary_five_seven_example_large_separators_A' = {0} := by decide

private theorem boundary_five_seven_example_large_separators_C_sdiff_C' :
  boundary_five_seven_example_large_separators_C \ boundary_five_seven_example_large_separators_C' =
  boundary_five_seven_example_large_separators_T := by decide

private lemma boundary_five_seven_example_large_separators_of_mem_A' {U W : Finset (Fin 28)}
    (hW : W.Nonempty) (hdisj : Disjoint U W)
    (hAC : ∀ u ∈ U, ∀ w ∈ W, ¬ in1122_fiveseven_graph.Adj u w)
    {u : Fin 28} (huU : u ∈ U) (huA' : u ∈ boundary_five_seven_example_large_separators_A') :
    U.card + W.card ≤ 14 := by
  have hW_sub_B : W ⊆ boundary_five_seven_example_large_separators_B := by
    intro w hw
    by_contra hwB
    have hne : w ≠ u := (Finset.disjoint_iff_ne.mp hdisj u huU w hw).symm
    have hadj := boundary_five_seven_example_large_separators_A'_adj u huA' w hwB hne
    exact hAC u huU w hw hadj
  by_cases hB' : ∃ b ∈ W, b ∈ boundary_five_seven_example_large_separators_B'
  · rcases hB' with ⟨b, hbW, hbB'⟩
    have hU_sub_A : U ⊆ boundary_five_seven_example_large_separators_A := by
      intro v hv
      by_contra hvA
      have hne : v ≠ b := Finset.disjoint_iff_ne.mp hdisj v hv b hbW
      have hadj := boundary_five_seven_example_large_separators_B'_adj b hbB' v hvA hne
      have hadj' := in1122_fiveseven_graph.adj_symm hadj
      exact hAC v hv b hbW hadj'
    have hUcard : U.card ≤ 5 := by
      have : boundary_five_seven_example_large_separators_A.card = 5 := by decide
      have := Finset.card_le_card hU_sub_A
      omega
    have hWcard : W.card ≤ 9 := by
      have : boundary_five_seven_example_large_separators_B.card = 9 := by decide
      have := Finset.card_le_card hW_sub_B
      omega
    omega
  · have hnot : ∀ b ∈ W, b ∉ boundary_five_seven_example_large_separators_B' := by
      intro b hb
      by_contra hbB'
      exact hB' ⟨b, hb, hbB'⟩
    have hW_sub_5 : W ⊆ {5} := by
      intro w hw
      have hwB := hW_sub_B hw
      have hnotw := hnot w hw
      have : w ∈ boundary_five_seven_example_large_separators_B \ boundary_five_seven_example_large_separators_B' :=
        Finset.mem_sdiff.mpr ⟨hwB, hnotw⟩
      rw [boundary_five_seven_example_large_separators_B_sdiff_B'] at this
      exact this
    have h5W : (5 : Fin 28) ∈ W := by
      rcases hW with ⟨w, hw⟩
      have := hW_sub_5 hw
      simp only [Finset.mem_singleton] at this
      subst this
      exact hw
    have hU_sub_nn5 : U ⊆ boundary_five_seven_example_large_separators_nn5 := by
      intro v hv
      have hne : v ≠ 5 := Finset.disjoint_iff_ne.mp hdisj v hv 5 h5W
      have hnotadj := hAC v hv 5 h5W
      have hnotadj' : ¬ in1122_fiveseven_graph.Adj 5 v := fun h => hnotadj (in1122_fiveseven_graph.adj_symm h)
      exact boundary_five_seven_example_large_separators_nn5_prop v hne hnotadj'
    have hUcard : U.card ≤ 8 := by
      have : boundary_five_seven_example_large_separators_nn5.card = 8 := by decide
      have := Finset.card_le_card hU_sub_nn5
      omega
    have hWcard : W.card ≤ 1 := by
      have : ({5} : Finset (Fin 28)).card = 1 := by decide
      have := Finset.card_le_card hW_sub_5
      omega
    omega

private lemma boundary_five_seven_example_large_separators_of_mem_B' {U W : Finset (Fin 28)}
    (hU : U.Nonempty) (hW : W.Nonempty) (hdisj : Disjoint U W)
    (hAC : ∀ u ∈ U, ∀ w ∈ W, ¬ in1122_fiveseven_graph.Adj u w)
    {u : Fin 28} (huU : u ∈ U) (huB' : u ∈ boundary_five_seven_example_large_separators_B') :
    U.card + W.card ≤ 14 := by
  have hW_sub_A : W ⊆ boundary_five_seven_example_large_separators_A := by
    intro w hw
    by_contra hwA
    have hne : w ≠ u := (Finset.disjoint_iff_ne.mp hdisj u huU w hw).symm
    have hadj := boundary_five_seven_example_large_separators_B'_adj u huB' w hwA hne
    exact hAC u huU w hw hadj
  by_cases hA' : ∃ a ∈ W, a ∈ boundary_five_seven_example_large_separators_A'
  · rcases hA' with ⟨a, haW, haA'⟩
    have hAC_rev : ∀ w ∈ W, ∀ v ∈ U, ¬ in1122_fiveseven_graph.Adj w v := by
      intro w hw v hv hadj
      exact hAC v hv w hw (in1122_fiveseven_graph.adj_symm hadj)
    have := boundary_five_seven_example_large_separators_of_mem_A' hU hdisj.symm hAC_rev haW haA'
    omega
  · have hnot : ∀ a ∈ W, a ∉ boundary_five_seven_example_large_separators_A' := by
      intro a ha
      by_contra haA'
      exact hA' ⟨a, ha, haA'⟩
    have hW_sub_0 : W ⊆ {0} := by
      intro w hw
      have hwA := hW_sub_A hw
      have hnotw := hnot w hw
      have : w ∈ boundary_five_seven_example_large_separators_A \ boundary_five_seven_example_large_separators_A' :=
        Finset.mem_sdiff.mpr ⟨hwA, hnotw⟩
      rw [boundary_five_seven_example_large_separators_A_sdiff_A'] at this
      exact this
    have h0W : (0 : Fin 28) ∈ W := by
      rcases hW with ⟨w, hw⟩
      have := hW_sub_0 hw
      simp only [Finset.mem_singleton] at this
      subst this
      exact hw
    have hU_sub_nn0 : U ⊆ boundary_five_seven_example_large_separators_nn0 := by
      intro v hv
      have hne : v ≠ 0 := Finset.disjoint_iff_ne.mp hdisj v hv 0 h0W
      have hnotadj := hAC v hv 0 h0W
      have hnotadj' : ¬ in1122_fiveseven_graph.Adj 0 v := fun h => hnotadj (in1122_fiveseven_graph.adj_symm h)
      exact boundary_five_seven_example_large_separators_nn0_prop v hne hnotadj'
    have hUcard : U.card ≤ 11 := by
      have : boundary_five_seven_example_large_separators_nn0.card = 11 := by decide
      have := Finset.card_le_card hU_sub_nn0
      omega
    have hWcard : W.card ≤ 1 := by
      have : ({0} : Finset (Fin 28)).card = 1 := by decide
      have := Finset.card_le_card hW_sub_0
      omega
    omega

private lemma boundary_five_seven_example_large_separators_of_mem_D {U W : Finset (Fin 28)}
    (hW : W.Nonempty) (hdisj : Disjoint U W)
    (hAC : ∀ u ∈ U, ∀ w ∈ W, ¬ in1122_fiveseven_graph.Adj u w)
    {u : Fin 28} (huU : u ∈ U) (huD : u ∈ boundary_five_seven_example_large_separators_D) :
    U.card + W.card ≤ 14 := by
  have hW_sub_C : W ⊆ boundary_five_seven_example_large_separators_C := by
    intro w hw
    by_contra hwC
    have hne : w ≠ u := (Finset.disjoint_iff_ne.mp hdisj u huU w hw).symm
    have hadj := boundary_five_seven_example_large_separators_D_adj u huD w hwC hne
    exact hAC u huU w hw hadj
  by_cases hC' : ∃ c ∈ W, c ∈ boundary_five_seven_example_large_separators_C'
  · rcases hC' with ⟨c, hcW, hcC'⟩
    have hU_sub_D : U ⊆ boundary_five_seven_example_large_separators_D := by
      intro v hv
      by_contra hvD
      have hne : v ≠ c := Finset.disjoint_iff_ne.mp hdisj v hv c hcW
      have hadj := boundary_five_seven_example_large_separators_C'_adj c hcC' v hvD hne
      have hadj' := in1122_fiveseven_graph.adj_symm hadj
      exact hAC v hv c hcW hadj'
    have hUcard : U.card ≤ 7 := by
      have : boundary_five_seven_example_large_separators_D.card = 7 := by decide
      have := Finset.card_le_card hU_sub_D
      omega
    have hWcard : W.card ≤ 7 := by
      have : boundary_five_seven_example_large_separators_C.card = 7 := by decide
      have := Finset.card_le_card hW_sub_C
      omega
    omega
  · have hnot : ∀ c ∈ W, c ∉ boundary_five_seven_example_large_separators_C' := by
      intro c hc
      by_contra hcC'
      exact hC' ⟨c, hc, hcC'⟩
    have hW_sub_T : W ⊆ boundary_five_seven_example_large_separators_T := by
      intro w hw
      have hwC := hW_sub_C hw
      have hnotw := hnot w hw
      have : w ∈ boundary_five_seven_example_large_separators_C \ boundary_five_seven_example_large_separators_C' :=
        Finset.mem_sdiff.mpr ⟨hwC, hnotw⟩
      rw [boundary_five_seven_example_large_separators_C_sdiff_C'] at this
      exact this
    rcases hW with ⟨w, hw⟩
    have hwT := hW_sub_T hw
    have hU_sub_nnw : U ⊆ boundary_five_seven_example_large_separators_nn w := by
      intro v hv
      have hne : v ≠ w := Finset.disjoint_iff_ne.mp hdisj v hv w hw
      have hnotadj := hAC v hv w hw
      simp only [boundary_five_seven_example_large_separators_nn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne, hnotadj⟩
    have hUcard : U.card ≤ 11 := by
      have hnn := boundary_five_seven_example_large_separators_T_nn w hwT
      have := Finset.card_le_card hU_sub_nnw
      omega
    have hWcard : W.card ≤ 3 := by
      have : boundary_five_seven_example_large_separators_T.card = 3 := by decide
      have := Finset.card_le_card hW_sub_T
      omega
    omega

theorem boundary_five_seven_example_large_separators :
    ∀ X U W : Finset (Fin 28), U.Nonempty → W.Nonempty →
      Disjoint X U → Disjoint X W → Disjoint U W → X ∪ U ∪ W = Finset.univ →
      (∀ u ∈ U, ∀ w ∈ W, ¬ in1122_fiveseven_graph.Adj u w) → 14 ≤ X.card := by
  intro X U W hU hW hXU hXW hUW huniv hAC
  have hUW_card : U.card + W.card ≤ 14 := by
    by_cases hA' : ∃ u ∈ U, u ∈ boundary_five_seven_example_large_separators_A'
    · rcases hA' with ⟨u, huU, huA'⟩
      exact boundary_five_seven_example_large_separators_of_mem_A' hW hUW hAC huU huA'
    by_cases hB' : ∃ u ∈ U, u ∈ boundary_five_seven_example_large_separators_B'
    · rcases hB' with ⟨u, huU, huB'⟩
      exact boundary_five_seven_example_large_separators_of_mem_B' hU hW hUW hAC huU huB'
    by_cases hD : ∃ u ∈ U, u ∈ boundary_five_seven_example_large_separators_D
    · rcases hD with ⟨u, huU, huD⟩
      exact boundary_five_seven_example_large_separators_of_mem_D hW hUW hAC huU huD
    by_cases hWA' : ∃ w ∈ W, w ∈ boundary_five_seven_example_large_separators_A'
    · rcases hWA' with ⟨w, hwW, hwA'⟩
      have hAC_rev : ∀ w ∈ W, ∀ u ∈ U, ¬ in1122_fiveseven_graph.Adj w u :=
        fun w hw u hu hadj => hAC u hu w hw (in1122_fiveseven_graph.adj_symm hadj)
      have := boundary_five_seven_example_large_separators_of_mem_A' hU hUW.symm hAC_rev hwW hwA'
      omega
    by_cases hWB' : ∃ w ∈ W, w ∈ boundary_five_seven_example_large_separators_B'
    · rcases hWB' with ⟨w, hwW, hwB'⟩
      have hAC_rev : ∀ w ∈ W, ∀ u ∈ U, ¬ in1122_fiveseven_graph.Adj w u :=
        fun w hw u hu hadj => hAC u hu w hw (in1122_fiveseven_graph.adj_symm hadj)
      have := boundary_five_seven_example_large_separators_of_mem_B' hW hU hUW.symm hAC_rev hwW hwB'
      omega
    by_cases hWD : ∃ w ∈ W, w ∈ boundary_five_seven_example_large_separators_D
    · rcases hWD with ⟨w, hwW, hwD⟩
      have hAC_rev : ∀ w ∈ W, ∀ u ∈ U, ¬ in1122_fiveseven_graph.Adj w u :=
        fun w hw u hu hadj => hAC u hu w hw (in1122_fiveseven_graph.adj_symm hadj)
      have := boundary_five_seven_example_large_separators_of_mem_D hU hUW.symm hAC_rev hwW hwD
      omega
    have hUW_sub_rem : U ∪ W ⊆ boundary_five_seven_example_large_separators_V_rem := by
      intro v hv
      simp only [Finset.mem_union] at hv
      have huniv_v : v ∈ boundary_five_seven_example_large_separators_A' ∪
                         boundary_five_seven_example_large_separators_B' ∪
                         boundary_five_seven_example_large_separators_D ∪
                         boundary_five_seven_example_large_separators_V_rem := by
        rw [boundary_five_seven_example_large_separators_univ_cover]; exact Finset.mem_univ v
      simp only [Finset.mem_union] at huniv_v
      rcases huniv_v with (((hvA' | hvB') | hvD) | hvrem)
      · rcases hv with hvU | hvW
        · exfalso; exact hA' ⟨v, hvU, hvA'⟩
        · exfalso; exact hWA' ⟨v, hvW, hvA'⟩
      · rcases hv with hvU | hvW
        · exfalso; exact hB' ⟨v, hvU, hvB'⟩
        · exfalso; exact hWB' ⟨v, hvW, hvB'⟩
      · rcases hv with hvU | hvW
        · exfalso; exact hD ⟨v, hvU, hvD⟩
        · exfalso; exact hWD ⟨v, hvW, hvD⟩
      · exact hvrem
    have hcard_le : (U ∪ W).card ≤ 9 := by
      have : boundary_five_seven_example_large_separators_V_rem.card = 9 := by decide
      have := Finset.card_le_card hUW_sub_rem
      omega
    rw [Finset.card_union_of_disjoint hUW] at hcard_le
    omega
  have hdisj : Disjoint (X ∪ U) W := by
    rw [Finset.disjoint_union_left]
    exact ⟨hXW, hUW⟩
  have hcard_all : (X ∪ U ∪ W).card = X.card + U.card + W.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hXU]
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard_all
  omega
