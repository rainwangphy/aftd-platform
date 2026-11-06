import AFTD.Prelude

/-!
# simple_graph_line_graph_triangle_star_or_root_triangle

Topic: graphs   Node: ffd3c2978eb3

Provenance: helper lemma. Triangle structure in the line-graph cover route.

Any triangle in the line graph of a finite simple graph comes from three root edges incident with a single root vertex or from the three edges of a root triangle.
-/

theorem simple_graph_line_graph_triangle_star_or_root_triangle
    (n : ℕ) (H : SimpleGraph (Fin n))
    (T : Finset H.edgeSet) (hT : H.lineGraph.IsNClique 3 T) :
    (∃ v : Fin n, ∀ e ∈ T, v ∈ e.val) ∨
      ∃ t : Finset (Fin n), H.IsNClique 3 t ∧
        ∀ e ∈ T, ∀ v ∈ e.val, v ∈ t := by
  classical
  obtain ⟨e1, e2, e3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp hT.card_eq
  have a12 := SimpleGraph.lineGraph_adj_iff_exists.mp
    (hT.isClique (by simp) (by simp) h12)
  have a13 := SimpleGraph.lineGraph_adj_iff_exists.mp
    (hT.isClique (by simp) (by simp) h13)
  have a23 := SimpleGraph.lineGraph_adj_iff_exists.mp
    (hT.isClique (by simp) (by simp) h23)
  obtain ⟨p, p1, p2⟩ := a12.2
  obtain ⟨q, q1, q3⟩ := a13.2
  obtain ⟨r, r2, r3⟩ := a23.2
  by_cases hpq : p = q
  · subst q
    left; refine ⟨p, ?_⟩
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  by_cases hpr : p = r
  · subst r
    left; refine ⟨p, ?_⟩
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  by_cases hqr : q = r
  · subst r
    left; refine ⟨q, ?_⟩
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have E1 : e1.val = s(p, q) := (Sym2.mem_and_mem_iff hpq).1 ⟨p1, q1⟩
  have E2 : e2.val = s(p, r) := (Sym2.mem_and_mem_iff hpr).1 ⟨p2, r2⟩
  have E3 : e3.val = s(q, r) := (Sym2.mem_and_mem_iff hqr).1 ⟨q3, r3⟩
  have hpq_adj : H.Adj p q := (SimpleGraph.mem_edgeSet H).mp (by simpa [E1] using e1.property)
  have hpr_adj : H.Adj p r := (SimpleGraph.mem_edgeSet H).mp (by simpa [E2] using e2.property)
  have hqr_adj : H.Adj q r := (SimpleGraph.mem_edgeSet H).mp (by simpa [E3] using e3.property)
  right
  refine ⟨{p, q, r}, ?_, ?_⟩
  · rw [SimpleGraph.isNClique_iff]
    constructor
    · simp [SimpleGraph.isClique_insert, SimpleGraph.isClique_pair, hpq_adj, hpr_adj, hqr_adj]
    · exact Finset.card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  · intro e he x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · rw [E1, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [E2, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
    · rw [E3, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
