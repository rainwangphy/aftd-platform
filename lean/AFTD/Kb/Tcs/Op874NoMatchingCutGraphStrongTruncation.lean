import AFTD.Prelude
import AFTD.Kb.Tcs.Op874TwelveVertexNoMatchingCutGraph
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.Op874TwelveVertexNoMatchingCutEdges
import AFTD.Kb.Tcs.MultigraphTruncation
import AFTD.Kb.Tcs.SimpleGraphIsStrongEdgeColoring

/-!
# op874_no_matching_cut_graph_strong_truncation

Topic: graphs   Node: 35f4a2c00c21

Provenance: helper lemma. Explicit coloring witness for the OP-874 no-perfect-matching-cut graph, experiment 35480.

The truncation of the displayed twelve-vertex graph without a perfect matching cut has a strong edge-coloring with six colors.
-/

/-- External (base-edge) colour of the six-colour local-state witness. -/
def op874_no_matching_cut_graph_strong_truncation_extColor (x : Sym2 (Fin 12)) : Fin 6 :=
  if x = s(0, 2) then 5
  else if x = s(0, 8) then 2
  else if x = s(0, 11) then 1
  else if x = s(1, 7) then 5
  else if x = s(1, 8) then 1
  else if x = s(1, 10) then 3
  else if x = s(2, 5) then 0
  else if x = s(2, 7) then 2
  else if x = s(3, 6) then 0
  else if x = s(3, 7) then 1
  else if x = s(3, 9) then 4
  else if x = s(4, 5) then 4
  else if x = s(4, 6) then 5
  else if x = s(4, 8) then 3
  else if x = s(5, 9) then 5
  else if x = s(6, 10) then 2
  else if x = s(9, 11) then 3
  else if x = s(10, 11) then 4
  else 0

/-- Hidden (port) colour at vertex `v` on the base edge `x`. -/
def op874_no_matching_cut_graph_strong_truncation_hidColor (v : Fin 12)
    (x : Sym2 (Fin 12)) : Fin 6 :=
  if v = 0 then
    (if x = s(0, 2) then 3 else if x = s(0, 8) then 4 else if x = s(0, 11) then 0 else 0)
  else if v = 1 then
    (if x = s(1, 7) then 4 else if x = s(1, 8) then 0 else if x = s(1, 10) then 2 else 0)
  else if v = 2 then
    (if x = s(0, 2) then 4 else if x = s(2, 5) then 1 else if x = s(2, 7) then 3 else 0)
  else if v = 3 then
    (if x = s(3, 6) then 3 else if x = s(3, 7) then 5 else if x = s(3, 9) then 2 else 0)
  else if v = 4 then
    (if x = s(4, 5) then 2 else if x = s(4, 6) then 1 else if x = s(4, 8) then 0 else 0)
  else if v = 5 then
    (if x = s(2, 5) then 3 else if x = s(4, 5) then 1 else if x = s(5, 9) then 2 else 0)
  else if v = 6 then
    (if x = s(3, 6) then 3 else if x = s(4, 6) then 4 else if x = s(6, 10) then 1 else 0)
  else if v = 7 then
    (if x = s(1, 7) then 0 else if x = s(2, 7) then 4 else if x = s(3, 7) then 3 else 0)
  else if v = 8 then
    (if x = s(0, 8) then 0 else if x = s(1, 8) then 4 else if x = s(4, 8) then 5 else 0)
  else if v = 9 then
    (if x = s(3, 9) then 2 else if x = s(5, 9) then 1 else if x = s(9, 11) then 0 else 0)
  else if v = 10 then
    (if x = s(1, 10) then 0 else if x = s(6, 10) then 1 else if x = s(10, 11) then 5 else 0)
  else
    (if x = s(0, 11) then 5 else if x = s(9, 11) then 2 else if x = s(10, 11) then 0 else 0)

/-- The three base edges at `v`. -/
def op874_no_matching_cut_graph_strong_truncation_ports (v : Fin 12) :
    Finset (Sym2 (Fin 12)) :=
  op874_twelve_vertex_no_matching_cut_edges.filter (fun x => v ∈ x)

/-- The three external colours at `v`. -/
def op874_no_matching_cut_graph_strong_truncation_extAt (v : Fin 12) : Finset (Fin 6) :=
  (op874_no_matching_cut_graph_strong_truncation_ports v).image
    (fun x => op874_no_matching_cut_graph_strong_truncation_extColor x)

/-- The three hidden port colours at `v`. -/
def op874_no_matching_cut_graph_strong_truncation_hidAt (v : Fin 12) : Finset (Fin 6) :=
  (op874_no_matching_cut_graph_strong_truncation_ports v).image
    (fun x => op874_no_matching_cut_graph_strong_truncation_hidColor v x)

/-- Every displayed edge is loopless. -/
theorem op874_no_matching_cut_graph_strong_truncation_nodiag :
    ∀ x ∈ op874_twelve_vertex_no_matching_cut_edges, ¬ x.IsDiag := by
  decide

/-- Every vertex lies on exactly three displayed edges. -/
theorem op874_no_matching_cut_graph_strong_truncation_cubic :
    ∀ v : Fin 12, (op874_no_matching_cut_graph_strong_truncation_ports v).card = 3 := by
  decide

/-- Distinct edges at a vertex get distinct external colours. -/
theorem op874_no_matching_cut_graph_strong_truncation_ext_inj :
    ∀ (v : Fin 12) (e f : Sym2 (Fin 12)),
      e ∈ op874_twelve_vertex_no_matching_cut_edges →
      f ∈ op874_twelve_vertex_no_matching_cut_edges → v ∈ e → v ∈ f →
      op874_no_matching_cut_graph_strong_truncation_extColor e
        = op874_no_matching_cut_graph_strong_truncation_extColor f → e = f := by
  decide

/-- Distinct edges at a vertex get distinct hidden port colours. -/
theorem op874_no_matching_cut_graph_strong_truncation_hid_inj :
    ∀ (v : Fin 12) (e f : Sym2 (Fin 12)),
      e ∈ op874_twelve_vertex_no_matching_cut_edges →
      f ∈ op874_twelve_vertex_no_matching_cut_edges → v ∈ e → v ∈ f →
      op874_no_matching_cut_graph_strong_truncation_hidColor v e
        = op874_no_matching_cut_graph_strong_truncation_hidColor v f → e = f := by
  decide

/-- No hidden port colour at a vertex equals an external colour there. -/
theorem op874_no_matching_cut_graph_strong_truncation_mix :
    ∀ (v : Fin 12) (e f : Sym2 (Fin 12)),
      e ∈ op874_twelve_vertex_no_matching_cut_edges →
      f ∈ op874_twelve_vertex_no_matching_cut_edges → v ∈ e → v ∈ f →
      op874_no_matching_cut_graph_strong_truncation_hidColor v e
        ≠ op874_no_matching_cut_graph_strong_truncation_extColor f := by
  decide

/-- A colour not used as an external colour at `v` is a hidden port colour there. -/
theorem op874_no_matching_cut_graph_strong_truncation_surj :
    ∀ (v : Fin 12) (ω : Fin 6),
      ω ∉ op874_no_matching_cut_graph_strong_truncation_extAt v →
      ω ∈ op874_no_matching_cut_graph_strong_truncation_hidAt v := by
  decide

/-- The exposed pairs at the two ends of every edge are disjoint. -/
theorem op874_no_matching_cut_graph_strong_truncation_disj :
    ∀ (x : Sym2 (Fin 12)), x ∈ op874_twelve_vertex_no_matching_cut_edges →
      ∀ u v : Fin 12, x = s(u, v) →
      Disjoint
        (op874_no_matching_cut_graph_strong_truncation_hidAt u \
          {op874_no_matching_cut_graph_strong_truncation_hidColor u x})
        (op874_no_matching_cut_graph_strong_truncation_hidAt v \
          {op874_no_matching_cut_graph_strong_truncation_hidColor v x}) := by
  decide

theorem op874_no_matching_cut_graph_strong_truncation :
    let G := op874_twelve_vertex_no_matching_cut_graph
    ∃ χ : Sym2 {q : (Fin 12) × G.edgeSet // q.1 ∈ (q.2 : Sym2 (Fin 12))} → Fin 6,
      simple_graph_is_strong_edge_coloring
        (multigraph_truncation (fun e : G.edgeSet => (e : Sym2 (Fin 12)))) χ := by
  dsimp only
  have hdiag := op874_no_matching_cut_graph_strong_truncation_nodiag
  have hcard := op874_no_matching_cut_graph_strong_truncation_cubic
  have hext := op874_no_matching_cut_graph_strong_truncation_ext_inj
  have hhid := op874_no_matching_cut_graph_strong_truncation_hid_inj
  have hmix := op874_no_matching_cut_graph_strong_truncation_mix
  have hsurj := op874_no_matching_cut_graph_strong_truncation_surj
  have hdisj := op874_no_matching_cut_graph_strong_truncation_disj
  have hedge : op874_twelve_vertex_no_matching_cut_graph.edgeSet
      = (↑op874_twelve_vertex_no_matching_cut_edges : Set (Sym2 (Fin 12))) := by
    rw [op874_twelve_vertex_no_matching_cut_graph, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, hdiag x h⟩⟩
  have hE0 : ∀ e : op874_twelve_vertex_no_matching_cut_graph.edgeSet,
      (e : Sym2 (Fin 12)) ∈ op874_twelve_vertex_no_matching_cut_edges := by
    intro e
    have h : (e : Sym2 (Fin 12))
        ∈ (↑op874_twelve_vertex_no_matching_cut_edges : Set (Sym2 (Fin 12))) := by
      rw [← hedge]
      exact e.2
    simpa using h
  have hloop : ∀ e : op874_twelve_vertex_no_matching_cut_graph.edgeSet,
      ¬ (e : Sym2 (Fin 12)).IsDiag := fun e => hdiag _ (hE0 e)
  have hcubic : ∀ v : Fin 12,
      Set.ncard {e : op874_twelve_vertex_no_matching_cut_graph.edgeSet
        | v ∈ (e : Sym2 (Fin 12))} = 3 := by
    intro v
    have h1 : {e : op874_twelve_vertex_no_matching_cut_graph.edgeSet
        | v ∈ (e : Sym2 (Fin 12))}.ncard
        = {x : Sym2 (Fin 12) | x ∈ op874_twelve_vertex_no_matching_cut_edges ∧ v ∈ x}.ncard := by
      refine Set.ncard_congr (fun e (_ : v ∈ (e : Sym2 (Fin 12))) => (e : Sym2 (Fin 12))) ?_ ?_ ?_
      · intro e he
        exact ⟨hE0 e, he⟩
      · intro e f he hf h
        exact Subtype.ext h
      · rintro x ⟨hx, hvx⟩
        exact ⟨⟨x, by rw [hedge]; simpa using hx⟩, hvx, rfl⟩
    have h2 : {x : Sym2 (Fin 12) | x ∈ op874_twelve_vertex_no_matching_cut_edges ∧ v ∈ x}
        = (↑(op874_no_matching_cut_graph_strong_truncation_ports v) :
            Set (Sym2 (Fin 12))) := by
      ext x
      simp [op874_no_matching_cut_graph_strong_truncation_ports]
    rw [h1, h2, Set.ncard_eq_toFinset_card', Finset.toFinset_coe]
    exact hcard v
  have hc : ∀ (v : Fin 12) (e f : op874_twelve_vertex_no_matching_cut_graph.edgeSet),
      v ∈ (e : Sym2 (Fin 12)) → v ∈ (f : Sym2 (Fin 12)) →
      op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12))
        = op874_no_matching_cut_graph_strong_truncation_extColor (f : Sym2 (Fin 12)) → e = f := by
    intro v e f he hf h
    exact Subtype.ext (hext v _ _ (hE0 e) (hE0 f) he hf h)
  have hh : ∀ (v : Fin 12) (e f : op874_twelve_vertex_no_matching_cut_graph.edgeSet),
      v ∈ (e : Sym2 (Fin 12)) → v ∈ (f : Sym2 (Fin 12)) →
      op874_no_matching_cut_graph_strong_truncation_hidColor v (e : Sym2 (Fin 12))
        = op874_no_matching_cut_graph_strong_truncation_hidColor v (f : Sym2 (Fin 12)) → e = f := by
    intro v e f he hf h
    exact Subtype.ext (hhid v _ _ (hE0 e) (hE0 f) he hf h)
  have hch : ∀ (v : Fin 12) (e f : op874_twelve_vertex_no_matching_cut_graph.edgeSet),
      v ∈ (e : Sym2 (Fin 12)) → v ∈ (f : Sym2 (Fin 12)) →
      op874_no_matching_cut_graph_strong_truncation_hidColor v (e : Sym2 (Fin 12))
        ≠ op874_no_matching_cut_graph_strong_truncation_extColor (f : Sym2 (Fin 12)) := by
    intro v e f he hf
    exact hmix v _ _ (hE0 e) (hE0 f) he hf
  have hcond : ∀ (e : op874_twelve_vertex_no_matching_cut_graph.edgeSet) (u v : Fin 12),
      (e : Sym2 (Fin 12)) = s(u, v) →
      op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12))
          = op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12)) ∧
        Disjoint
          (truncation_exposed_pair (fun e : op874_twelve_vertex_no_matching_cut_graph.edgeSet =>
            (e : Sym2 (Fin 12)))
            (fun v e => op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12)))
            (fun v e => op874_no_matching_cut_graph_strong_truncation_hidColor v (e : Sym2 (Fin 12)))
            u e)
          (truncation_exposed_pair (fun e : op874_twelve_vertex_no_matching_cut_graph.edgeSet =>
            (e : Sym2 (Fin 12)))
            (fun v e => op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12)))
            (fun v e => op874_no_matching_cut_graph_strong_truncation_hidColor v (e : Sym2 (Fin 12)))
            v e) := by
    intro e u v huv
    refine ⟨rfl, ?_⟩
    rw [Set.disjoint_left]
    intro ω hA hB
    simp only [truncation_exposed_pair, Set.mem_setOf_eq] at hA hB
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨hB1, hB2⟩ := hB
    have hAu : ω ∉ op874_no_matching_cut_graph_strong_truncation_extAt u := by
      intro hmem
      obtain ⟨y, hy, hyω⟩ := Finset.mem_image.mp hmem
      obtain ⟨hyE, huy⟩ := Finset.mem_filter.mp hy
      exact (hA1 ⟨y, by rw [hedge]; simpa using hyE⟩ huy) hyω
    have hAv : ω ∉ op874_no_matching_cut_graph_strong_truncation_extAt v := by
      intro hmem
      obtain ⟨y, hy, hyω⟩ := Finset.mem_image.mp hmem
      obtain ⟨hyE, huy⟩ := Finset.mem_filter.mp hy
      exact (hB1 ⟨y, by rw [hedge]; simpa using hyE⟩ huy) hyω
    have h1 : ω ∈ op874_no_matching_cut_graph_strong_truncation_hidAt u := hsurj u ω hAu
    have h2 : ω ∈ op874_no_matching_cut_graph_strong_truncation_hidAt v := hsurj v ω hAv
    have h3 : ω ∉ ({op874_no_matching_cut_graph_strong_truncation_hidColor u
        (e : Sym2 (Fin 12))} : Finset (Fin 6)) := by
      simpa using hA2
    have h4 : ω ∉ ({op874_no_matching_cut_graph_strong_truncation_hidColor v
        (e : Sym2 (Fin 12))} : Finset (Fin 6)) := by
      simpa using hB2
    exact (Finset.disjoint_left.mp (hdisj (e : Sym2 (Fin 12)) (hE0 e) u v huv))
      (Finset.mem_sdiff.mpr ⟨h1, h3⟩) (Finset.mem_sdiff.mpr ⟨h2, h4⟩)
  obtain ⟨χ, hχ, -⟩ := (truncation_local_states_strong_coloring_iff (V := Fin 12)
    (E := op874_twelve_vertex_no_matching_cut_graph.edgeSet) (Ω := Fin 6) (by decide)
    (fun e => (e : Sym2 (Fin 12))) hloop hcubic
    (fun v e => op874_no_matching_cut_graph_strong_truncation_extColor (e : Sym2 (Fin 12)))
    (fun v e => op874_no_matching_cut_graph_strong_truncation_hidColor v (e : Sym2 (Fin 12)))
    hc hh hch).mpr hcond
  exact ⟨χ, hχ⟩
