import AFTD.Prelude

/-!
# simple_graph_rich_neighbor_five_subdivide_three_palette

Topic: graphs   Node: 71bb2313e8ad

Provenance: helper lemma. Helper for OP-309 (arXiv:2610.21868, Conjecture 1.1). This is only the local palette contract, without graph transport. All 144 normalized proper boundary cases were independently checked in experiment 4659.

Scalar five-color contract for replacing a cubic edge by a four-edge path and three pendant edges: every new internal vertex has an incident rich path edge; both end edges remain rich when the old boundary was rich.
-/

private lemma simple_graph_rich_neighbor_five_subdivide_three_palette_distinct (x : Fin 5) :
    ∃ y z a b : Fin 5, [x,y,z,a,b].Pairwise (· ≠ ·) := by
  let σ := Equiv.swap (0 : Fin 5) x
  refine ⟨σ 1, σ 2, σ 3, σ 4, ?_⟩
  have hx : σ 0 = x := by simp [σ]
  rw [← hx]
  have h : ([0,1,2,3,4] : List (Fin 5)).Pairwise (· ≠ ·) := by decide
  exact h.map σ (fun _ _ hne => σ.injective.ne hne)

theorem simple_graph_rich_neighbor_five_subdivide_three_palette
    (x a b c d : Fin 5)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ y z A B C : Fin 5,
      [x,y,A].Pairwise (· ≠ ·) ∧
      [y,z,B].Pairwise (· ≠ ·) ∧
      [z,x,C].Pairwise (· ≠ ·) ∧
      (([a,b,y,A].Pairwise (· ≠ ·)) ∨ ([x,A,z,B].Pairwise (· ≠ ·))) ∧
      (([x,A,z,B].Pairwise (· ≠ ·)) ∨ ([y,B,x,C].Pairwise (· ≠ ·))) ∧
      (([y,B,x,C].Pairwise (· ≠ ·)) ∨ ([z,C,c,d].Pairwise (· ≠ ·))) ∧
      ([a,b,c,d].Pairwise (· ≠ ·) →
        [a,b,y,A].Pairwise (· ≠ ·) ∧ [z,C,c,d].Pairwise (· ≠ ·)) := by
  by_cases h : [a,b,c,d].Pairwise (· ≠ ·)
  · refine ⟨c,a,d,b,b, ?_⟩
    simp_all [List.pairwise_cons, ne_comm]
  · obtain ⟨y,z,A,B,hfive⟩ := simple_graph_rich_neighbor_five_subdivide_three_palette_distinct x
    refine ⟨y,z,A,B,A, ?_⟩
    simp_all [List.pairwise_cons, ne_comm]
