import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphMaximumTrianglePackingEdgeMeets
import AFTD.Kb.Tcs.SimpleGraphK4AttachmentOfTwoTriangleEdgeCovers

/-!
# simple_graph_opposite_pair_stable_k4_attachment

Topic: graphs   Node: 92a48c820353

Provenance: helper lemma. Structural reduction of the pair-stable forced-K4 branch of simple_graph_triangle_cover_number_le_two_mul_packing_number.

Let P be a maximum edge-disjoint triangle packing containing abc, and let x complete abc to a four-clique. Suppose neither ax nor bx is an edge of any packed triangle. If deleting the opposite edges ab and cx preserves the packing number, then another triangle t of P contains a vertex y outside the four-clique and either t contains a or b and xy is an edge, or t contains x and ay or by is an edge.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem stable_k4_attachment_in604
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Finset (Fin n))) (a b c x : Fin n)
    (htri : ∀ t ∈ P, G.IsNClique 3 t)
    (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1))
    (hmax : P.card = simple_graph_triangle_packing_number G)
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n)))
    (hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t))
    (hstable : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) =
      simple_graph_triangle_packing_number G) :
    ∃ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) ∧ ∃ y ∈ t,
      y ∉ ({a,b,c,x} : Finset (Fin n)) ∧
      (((a ∈ t ∨ b ∈ t) ∧ G.Adj x y) ∨
        (x ∈ t ∧ (G.Adj a y ∨ G.Adj b y))) := by
  classical
  let H := G.deleteEdges {s(a,b), s(c,x)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le (G := G) {s(a,b), s(c,x)}
  let A : Set ℕ := {k | ∃ Q : Finset (Finset (Fin n)),
    (∀ t ∈ Q, H.IsNClique 3 t) ∧
    (Q : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ Q.card = k}
  have hne : A.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  have hbdd : BddAbove A := by
    refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
    rintro k ⟨Q, _, _, rfl⟩
    exact Finset.card_le_univ Q
  obtain ⟨Q, hQH, hQpair, hQcard⟩ := Nat.sSup_mem hne hbdd
  have hQcard' : Q.card = simple_graph_triangle_packing_number G := by
    change Q.card = simple_graph_triangle_packing_number H at hQcard
    change simple_graph_triangle_packing_number H = simple_graph_triangle_packing_number G at hstable
    omega
  have hQG : ∀ t ∈ Q, G.IsNClique 3 t := by
    intro t ht; exact (hQH t ht).mono hHG
  have hPc := simple_graph_maximum_triangle_packing_edge_meets G P htri hdisj hmax
  have hQc := simple_graph_maximum_triangle_packing_edge_meets G Q hQG hQpair hQcard'
  have hab : a ≠ b := by
    intro h; subst b
    have hsub : ({a,a,c,x} : Finset (Fin n)) ⊆ {a,c,x} := by simp
    have hc := Finset.card_le_card hsub
    have h3 := Finset.card_le_three (a := a) (b := c) (c := x)
    have h4 := hk4.card_eq
    omega
  have hcx : c ≠ x := by
    intro h; subst x
    have hsub : ({a,b,c,c} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; aesop
    have hc := Finset.card_le_card hsub
    have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have havoid : ∀ t ∈ Q, ¬ (a ∈ t ∧ b ∈ t) ∧ ¬ (c ∈ t ∧ x ∈ t) := by
    intro t ht
    constructor
    · intro h
      have hadj : H.Adj a b := (hQH t ht).isClique h.1 h.2 hab
      have hnot := (SimpleGraph.deleteEdges_adj.mp hadj).2
      exact hnot (by simp)
    · intro h
      have hadj : H.Adj c x := (hQH t ht).isClique h.1 h.2 hcx
      have hnot := (SimpleGraph.deleteEdges_adj.mp hadj).2
      exact hnot (by simp)
  exact simple_graph_k4_attachment_of_two_triangle_edge_covers n G P Q a b c x hk4 hPc hQc hQG hspokes havoid

theorem simple_graph_opposite_pair_stable_k4_attachment (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (a b c x : Fin n) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hmax : P.card = simple_graph_triangle_packing_number G) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t)) (hstable : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b), s(c,x)}) = simple_graph_triangle_packing_number G) : ∃ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) ∧ ∃ y ∈ t, y ∉ ({a,b,c,x} : Finset (Fin n)) ∧ (((a ∈ t ∨ b ∈ t) ∧ G.Adj x y) ∨ (x ∈ t ∧ (G.Adj a y ∨ G.Adj b y))) := by
  exact stable_k4_attachment_in604 n G P a b c x htri hdisj hmax hk4 hspokes hstable
