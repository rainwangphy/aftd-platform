import AFTD.Prelude
import AFTD.Kb.Tcs.HSubdividedK33

/-!
# subdivided_k33_line_graph_chromatic_number_eq_four

Topic: graphs   Node: bb8b482eaf2c

Provenance: helper lemma. Helper for arXiv:2610.32404 Proposition 11.2 (PR-412).

The line graph of the graph obtained by subdividing one edge of K3,3 once has chromatic number exactly four.
-/

private def subdivided_k33_line_graph_chromatic_number_eq_four_gcol (a b : Fin 7) : Fin 4 :=
  if (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 0) then 0
  else if (a = 3 ∧ b = 6) ∨ (a = 6 ∧ b = 3) then 3
  else if (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) then 1
  else if (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 0) then 2
  else if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then 2
  else if (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) then 0
  else if (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1) then 1
  else if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1
  else if (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) then 2
  else if (a = 2 ∧ b = 5) ∨ (a = 5 ∧ b = 2) then 0
  else 0

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm :
    ∀ a b : Fin 7, subdivided_k33_line_graph_chromatic_number_eq_four_gcol a b
      = subdivided_k33_line_graph_chromatic_number_eq_four_gcol b a := by decide

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_gcol_adj_ne :
    ∀ v x y : Fin 7, h_subdivided_k33.Adj v x → h_subdivided_k33.Adj v y → x ≠ y →
      subdivided_k33_line_graph_chromatic_number_eq_four_gcol v x
        ≠ subdivided_k33_line_graph_chromatic_number_eq_four_gcol v y := by
  have h0 : ∀ x : Fin 7, h_subdivided_k33.Adj (0:Fin 7) x → (x = 6 ∨ x = 4 ∨ x = 5) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h1 : ∀ x : Fin 7, h_subdivided_k33.Adj (1:Fin 7) x → (x = 3 ∨ x = 4 ∨ x = 5) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h2 : ∀ x : Fin 7, h_subdivided_k33.Adj (2:Fin 7) x → (x = 3 ∨ x = 4 ∨ x = 5) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h3 : ∀ x : Fin 7, h_subdivided_k33.Adj (3:Fin 7) x → (x = 6 ∨ x = 1 ∨ x = 2) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h4 : ∀ x : Fin 7, h_subdivided_k33.Adj (4:Fin 7) x → (x = 0 ∨ x = 1 ∨ x = 2) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h5 : ∀ x : Fin 7, h_subdivided_k33.Adj (5:Fin 7) x → (x = 0 ∨ x = 1 ∨ x = 2) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  have h6 : ∀ x : Fin 7, h_subdivided_k33.Adj (6:Fin 7) x → (x = 0 ∨ x = 3) := by
    intro x hx; simp only [h_subdivided_k33, SimpleGraph.fromRel] at hx; omega
  intro v x y hx hy hxy
  fin_cases v
  · rcases h0 x hx with rfl | rfl | rfl <;> rcases h0 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h1 x hx with rfl | rfl | rfl <;> rcases h1 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h2 x hx with rfl | rfl | rfl <;> rcases h2 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h3 x hx with rfl | rfl | rfl <;> rcases h3 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h4 x hx with rfl | rfl | rfl <;> rcases h4 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h5 x hx with rfl | rfl | rfl <;> rcases h5 y hy with rfl | rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]
  · rcases h6 x hx with rfl | rfl <;> rcases h6 y hy with rfl | rfl <;>
      simp_all [subdivided_k33_line_graph_chromatic_number_eq_four_gcol]

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_edge_col_aux :
    ∀ (a b c d v : Fin 7), h_subdivided_k33.Adj a b → h_subdivided_k33.Adj c d →
      v ∈ s(a,b) → v ∈ s(c,d) → s(a,b) ≠ s(c,d) →
      subdivided_k33_line_graph_chromatic_number_eq_four_gcol a b
        ≠ subdivided_k33_line_graph_chromatic_number_eq_four_gcol c d := by
  intro a b c d v hab hcd hv1 hv2 hne
  rw [Sym2.mem_iff] at hv1 hv2
  rcases hv1 with hva | hvb
  · subst v
    rcases hv2 with hac | had
    · subst c
      exact subdivided_k33_line_graph_chromatic_number_eq_four_gcol_adj_ne a b d hab hcd
        (by intro h; exact hne (by rw [h]))
    · subst d
      rw [subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm c a]
      exact subdivided_k33_line_graph_chromatic_number_eq_four_gcol_adj_ne a b c hab hcd.symm
        (by rintro rfl; exact hne Sym2.eq_swap)
  · subst v
    rcases hv2 with hbc | hbd
    · subst c
      rw [subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm a b]
      exact subdivided_k33_line_graph_chromatic_number_eq_four_gcol_adj_ne b a d hab.symm hcd
        (by rintro rfl; exact hne Sym2.eq_swap)
    · subst d
      rw [subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm a b,
        subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm c b]
      exact subdivided_k33_line_graph_chromatic_number_eq_four_gcol_adj_ne b a c hab.symm hcd.symm
        (by rintro rfl; exact hne rfl)

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_colorable_four :
    h_subdivided_k33.lineGraph.Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun e : ↑h_subdivided_k33.edgeSet =>
      Sym2.lift ⟨subdivided_k33_line_graph_chromatic_number_eq_four_gcol,
        subdivided_k33_line_graph_chromatic_number_eq_four_gcol_symm⟩ (e : Sym2 (Fin 7))) ?_⟩
  intro e1 e2 hAdj
  obtain ⟨hne, v, hv1, hv2⟩ := hAdj
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective (e1 : Sym2 (Fin 7))
  obtain ⟨⟨c, d⟩, hcd⟩ := Sym2.mk_surjective (e2 : Sym2 (Fin 7))
  have hab' : s(a, b) = (e1 : Sym2 (Fin 7)) := hab
  have hcd' : s(c, d) = (e2 : Sym2 (Fin 7)) := hcd
  have h1' : h_subdivided_k33.Adj a b := by
    have hmem : Sym2.mk a b ∈ h_subdivided_k33.edgeSet := hab'.symm ▸ e1.2
    exact (SimpleGraph.mem_edgeSet h_subdivided_k33).mp hmem
  have h2' : h_subdivided_k33.Adj c d := by
    have hmem : Sym2.mk c d ∈ h_subdivided_k33.edgeSet := hcd'.symm ▸ e2.2
    exact (SimpleGraph.mem_edgeSet h_subdivided_k33).mp hmem
  have hv1' : v ∈ s(a, b) := by rwa [← hab'] at hv1
  have hv2' : v ∈ s(c, d) := by rwa [← hcd'] at hv2
  have hne' : s(a, b) ≠ s(c, d) := by
    intro h
    exact hne (Subtype.ext (by rw [← hab', ← hcd']; exact h))
  rw [show (e1 : Sym2 (Fin 7)) = s(a, b) from hab'.symm,
    show (e2 : Sym2 (Fin 7)) = s(c, d) from hcd'.symm, Sym2.lift_mk, Sym2.lift_mk]
  exact subdivided_k33_line_graph_chromatic_number_eq_four_edge_col_aux a b c d v h1' h2' hv1' hv2' hne'

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj {V : Type}
    (G : SimpleGraph V) {a b c d : V} (v : V) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (h1 : v ∈ s(a, b)) (h2 : v ∈ s(c, d)) :
    G.lineGraph.Adj ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hab⟩
      ⟨s(c, d), (SimpleGraph.mem_edgeSet G).mpr hcd⟩ := by
  refine ⟨?_, ⟨v, h1, h2⟩⟩
  simp only [ne_eq, Subtype.mk.injEq]
  exact hne

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_fin3_no_color
    (c06 c36 c04 c05 c13 c14 c15 c23 c24 c25 : Fin 3)
    (h1 : c06 ≠ c04) (h2 : c06 ≠ c05) (h3 : c04 ≠ c05)
    (h4 : c04 ≠ c14) (h5 : c04 ≠ c24) (h6 : c14 ≠ c24)
    (h7 : c05 ≠ c15) (h8 : c05 ≠ c25) (h9 : c15 ≠ c25)
    (h10 : c13 ≠ c14) (h11 : c13 ≠ c15) (h12 : c14 ≠ c15)
    (h13 : c23 ≠ c24) (h14 : c23 ≠ c25) (h15 : c24 ≠ c25)
    (h16 : c36 ≠ c13) (h17 : c36 ≠ c23) (h18 : c13 ≠ c23)
    (h19 : c06 ≠ c36) : False := by
  fin_cases c06 <;> fin_cases c04 <;> fin_cases c05 <;> simp_all <;>
  fin_cases c14 <;> simp_all <;>
  fin_cases c24 <;> simp_all <;>
  fin_cases c15 <;> simp_all <;>
  fin_cases c25 <;> simp_all <;>
  fin_cases c13 <;> simp_all <;>
  fin_cases c23 <;> simp_all <;>
  fin_cases c36 <;> simp_all

private lemma subdivided_k33_line_graph_chromatic_number_eq_four_not_colorable_three :
    ¬ h_subdivided_k33.lineGraph.Colorable 3 := by
  rintro ⟨C⟩
  have h06 : h_subdivided_k33.Adj (0:Fin 7) 6 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h36 : h_subdivided_k33.Adj (3:Fin 7) 6 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h04 : h_subdivided_k33.Adj (0:Fin 7) 4 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h05 : h_subdivided_k33.Adj (0:Fin 7) 5 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h13 : h_subdivided_k33.Adj (1:Fin 7) 3 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h14 : h_subdivided_k33.Adj (1:Fin 7) 4 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h15 : h_subdivided_k33.Adj (1:Fin 7) 5 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h23 : h_subdivided_k33.Adj (2:Fin 7) 3 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h24 : h_subdivided_k33.Adj (2:Fin 7) 4 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  have h25 : h_subdivided_k33.Adj (2:Fin 7) 5 := by simp [h_subdivided_k33, SimpleGraph.fromRel]
  let e06 : ↑h_subdivided_k33.edgeSet := ⟨s(0,6), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h06⟩
  let e36 : ↑h_subdivided_k33.edgeSet := ⟨s(3,6), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h36⟩
  let e04 : ↑h_subdivided_k33.edgeSet := ⟨s(0,4), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h04⟩
  let e05 : ↑h_subdivided_k33.edgeSet := ⟨s(0,5), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h05⟩
  let e13 : ↑h_subdivided_k33.edgeSet := ⟨s(1,3), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h13⟩
  let e14 : ↑h_subdivided_k33.edgeSet := ⟨s(1,4), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h14⟩
  let e15 : ↑h_subdivided_k33.edgeSet := ⟨s(1,5), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h15⟩
  let e23 : ↑h_subdivided_k33.edgeSet := ⟨s(2,3), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h23⟩
  let e24 : ↑h_subdivided_k33.edgeSet := ⟨s(2,4), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h24⟩
  let e25 : ↑h_subdivided_k33.edgeSet := ⟨s(2,5), (SimpleGraph.mem_edgeSet h_subdivided_k33).mpr h25⟩
  have c1 : C e06 ≠ C e04 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 0 h06 h04 (by simp) (by simp) (by simp))
  have c2 : C e06 ≠ C e05 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 0 h06 h05 (by simp) (by simp) (by simp))
  have c3 : C e04 ≠ C e05 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 0 h04 h05 (by simp) (by simp) (by simp))
  have c4 : C e04 ≠ C e14 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 4 h04 h14 (by simp) (by simp) (by simp))
  have c5 : C e04 ≠ C e24 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 4 h04 h24 (by simp) (by simp) (by simp))
  have c6 : C e14 ≠ C e24 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 4 h14 h24 (by simp) (by simp) (by simp))
  have c7 : C e05 ≠ C e15 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 5 h05 h15 (by simp) (by simp) (by simp))
  have c8 : C e05 ≠ C e25 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 5 h05 h25 (by simp) (by simp) (by simp))
  have c9 : C e15 ≠ C e25 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 5 h15 h25 (by simp) (by simp) (by simp))
  have c10 : C e13 ≠ C e14 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 1 h13 h14 (by simp) (by simp) (by simp))
  have c11 : C e13 ≠ C e15 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 1 h13 h15 (by simp) (by simp) (by simp))
  have c12 : C e14 ≠ C e15 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 1 h14 h15 (by simp) (by simp) (by simp))
  have c13 : C e23 ≠ C e24 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 2 h23 h24 (by simp) (by simp) (by simp))
  have c14 : C e23 ≠ C e25 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 2 h23 h25 (by simp) (by simp) (by simp))
  have c15 : C e24 ≠ C e25 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 2 h24 h25 (by simp) (by simp) (by simp))
  have c16 : C e36 ≠ C e13 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 3 h36 h13 (by simp) (by simp) (by simp))
  have c17 : C e36 ≠ C e23 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 3 h36 h23 (by simp) (by simp) (by simp))
  have c18 : C e13 ≠ C e23 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 3 h13 h23 (by simp) (by simp) (by simp))
  have c19 : C e06 ≠ C e36 := C.map_adj (subdivided_k33_line_graph_chromatic_number_eq_four_line_graph_adj h_subdivided_k33 6 h06 h36 (by simp) (by simp) (by simp))
  exact subdivided_k33_line_graph_chromatic_number_eq_four_fin3_no_color
    (C e06) (C e36) (C e04) (C e05) (C e13) (C e14) (C e15) (C e23) (C e24) (C e25)
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19

theorem subdivided_k33_line_graph_chromatic_number_eq_four : h_subdivided_k33.lineGraph.chromaticNumber = 4 := (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable
    (G := h_subdivided_k33.lineGraph) (n := 3)).mpr
    ⟨subdivided_k33_line_graph_chromatic_number_eq_four_colorable_four,
     subdivided_k33_line_graph_chromatic_number_eq_four_not_colorable_three⟩
