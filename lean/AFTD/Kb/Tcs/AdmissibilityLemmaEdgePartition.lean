import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEndpointSumEdges

/-!
# admissibility_lemma_edge_partition

Topic: graphs   Node: a516529d59b9

Provenance: helper lemma. arXiv:2611.16338, Lemma 2.1

Let s ≥ 3 and let φ : V → ℕ be a vertex labeling of a finite simple graph G such that every vertex receives label 1 or s. Then the edge set of G is partitioned into the classes of edges with endpoint label sums 2, s + 1, and 2s, so that |E_2| + |E_{s+1}| + |E_{2s}| = |E(G)|.
-/

private lemma admissibility_lemma_edge_partition_three_fibers
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (r1 r2 r3 : ℕ)
    (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h23 : r2 ≠ r3)
    (hall : ∀ x ∈ s, f x = r1 ∨ f x = r2 ∨ f x = r3) :
    (s.filter (fun x => f x = r1)).card +
    (s.filter (fun x => f x = r2)).card +
    (s.filter (fun x => f x = r3)).card = s.card := by
  set A := s.filter (fun x => f x = r1)
  set B := s.filter (fun x => f x = r2)
  set C := s.filter (fun x => f x = r3)
  have dAB : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro x _ hx1 hx2
    subst hx1 hx2
    exact h12 rfl
  have dAC : Disjoint A C := by
    rw [Finset.disjoint_filter]
    intro x _ hx1 hx3
    subst hx1 hx3
    exact h13 rfl
  have dBC : Disjoint B C := by
    rw [Finset.disjoint_filter]
    intro x _ hx2 hx3
    subst hx2 hx3
    exact h23 rfl
  have d_union : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_union_left]
    exact ⟨dAC, dBC⟩
  have h_card_AB : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint dAB
  have h_card_all : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card := Finset.card_union_of_disjoint d_union
  rw [h_card_AB] at h_card_all
  have h_union : (A ∪ B) ∪ C = s := by
    have h_or : (A ∪ B) ∪ C = s.filter (fun x => (f x = r1 ∨ f x = r2) ∨ f x = r3) := by
      simp only [A, B, C, Finset.filter_or]
    rw [h_or]
    apply Finset.filter_true_of_mem
    intro x hx
    rcases hall x hx with h1 | h2 | h3
    · left; left; exact h1
    · left; right; exact h2
    · right; exact h3
  rw [h_union] at h_card_all
  change A.card + B.card + C.card = s.card
  linarith

open scoped Classical in
/-- A binary {1, s}-labeling partitions E(G) into classes E_2, E_{s+1}, E_{2s}. -/
theorem admissibility_lemma_edge_partition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) (hs : 3 ≤ s) (φ : V → ℕ)
    (hφ : ∀ v : V, φ v = 1 ∨ φ v = s) :
    let a := (simple_graph_endpoint_sum_edges G φ 2).card
    let b := (simple_graph_endpoint_sum_edges G φ (s + 1)).card
    let c := (simple_graph_endpoint_sum_edges G φ (2 * s)).card
    a + b + c = G.edgeFinset.card := by
  intro a b c
  change (simple_graph_endpoint_sum_edges G φ 2).card +
    (simple_graph_endpoint_sum_edges G φ (s + 1)).card +
    (simple_graph_endpoint_sum_edges G φ (2 * s)).card = G.edgeFinset.card
  simp only [simple_graph_endpoint_sum_edges]
  apply admissibility_lemma_edge_partition_three_fibers G.edgeFinset
    (fun e => Sym2.lift ⟨fun u v => φ u + φ v, fun _ _ => add_comm _ _⟩ e)
    2 (s + 1) (2 * s)
  · omega
  · omega
  · omega
  · intro e he
    refine Sym2.inductionOn e fun u v => ?_
    dsimp
    rcases hφ u with hu | hu <;> rcases hφ v with hv | hv
    · left; rw [hu, hv]
    · right; left; rw [hu, hv, add_comm]
    · right; left; rw [hu, hv]
    · right; right; rw [hu, hv, two_mul]
