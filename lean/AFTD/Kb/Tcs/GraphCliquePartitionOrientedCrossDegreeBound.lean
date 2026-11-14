import AFTD.Prelude

/-!
# graph_clique_partition_oriented_cross_degree_bound

Topic: graphs   Node: a76b102d4943

Provenance: helper lemma. Degree-counting bridge for OP-110 and the exceptional-vertex reductions.

If the color classes of a finite graph are cliques and an oriented digraph is a spanning subgraph, then twice its number of crossing arcs plus the sum of the products of each color-class size and its predecessor is at most twice the number of graph edges.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem graph_clique_partition_oriented_cross_degree_bound
    (α κ : Type) [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (D : Digraph α) [DecidableRel D.Adj] (col : α → κ)
    (hclique : ∀ u v, col u = col v → u ≠ v → G.Adj u v)
    (hsub : ∀ u v, D.Adj u v → G.Adj u v)
    (hori : ∀ u v, D.Adj u v → ¬ D.Adj v u) :
    (∑ i : κ, (Finset.univ.filter fun v => col v = i).card *
      ((Finset.univ.filter fun v => col v = i).card - 1)) +
    2 * (∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card) ≤
      2 * G.edgeFinset.card := by
  classical
  let S : κ → Finset (α) := fun i => Finset.univ.filter fun v => col v = i
  let n : κ → ℕ := fun i => (S i).card
  let inside : α → Finset (α) := fun v => (S (col v)).erase v
  let out : α → Finset (α) := fun v =>
    Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w
  let inc : α → Finset (α) := fun v =>
    Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj w v
  have hlocal (v : α) : (inside v).card + (out v).card + (inc v).card ≤ G.degree v := by
    have hab : Disjoint (inside v) (out v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : col w = col v := (Finset.mem_filter.mp (Finset.mem_erase.mp hw1).2).2
      have h2 : col w ≠ col v := (Finset.mem_filter.mp hw2).2.1
      exact h2 h1
    have hac : Disjoint (inside v) (inc v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : col w = col v := (Finset.mem_filter.mp (Finset.mem_erase.mp hw1).2).2
      have h2 : col w ≠ col v := (Finset.mem_filter.mp hw2).2.1
      exact h2 h1
    have hbc : Disjoint (out v) (inc v) := by
      apply Finset.disjoint_left.mpr
      intro w hw1 hw2
      have h1 : D.Adj v w := (Finset.mem_filter.mp hw1).2.2
      have h2 : D.Adj w v := (Finset.mem_filter.mp hw2).2.2
      exact hori v w h1 h2
    have hall : Disjoint (inside v) (out v ∪ inc v) := Finset.disjoint_union_right.mpr ⟨hab, hac⟩
    have hsubset : inside v ∪ (out v ∪ inc v) ⊆ G.neighborFinset v := by
      intro w hw
      simp only [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_union.mp hw with ha | ha
      · have hw' := Finset.mem_erase.mp ha
        have hc : col w = col v := (Finset.mem_filter.mp hw'.2).2
        exact hclique v w hc.symm hw'.1.symm
      · rcases Finset.mem_union.mp ha with hb | hc
        · exact hsub v w (Finset.mem_filter.mp hb).2.2
        · exact (hsub w v (Finset.mem_filter.mp hc).2.2).symm
    have hh := Finset.card_le_card hsubset
    rw [Finset.card_union_of_disjoint hall, Finset.card_union_of_disjoint hbc] at hh
    change _ ≤ G.degree v at hh
    omega
  have hcount (v : α) : (inside v).card = n (col v) - 1 := by
    apply Finset.card_erase_of_mem
    simp [S]
  have hinside : (∑ v : α, (inside v).card) = ∑ i : κ, n i * (n i - 1) := by
    simp_rw [hcount]
    rw [← Finset.sum_fiberwise Finset.univ col]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ v ∈ Finset.univ.filter (fun v => col v = i), (n (col v) - 1)) =
          ∑ _v ∈ Finset.univ.filter (fun v => col v = i), (n i - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [(Finset.mem_filter.mp hv).2]
      _ = n i * (n i - 1) := by simp [n,S]
  have hcross : (∑ v : α, (out v).card) = ∑ v : α, (inc v).card := by
    simp only [out, inc, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    by_cases h : col w = col v <;> by_cases hd : D.Adj v w <;> simp [h, Ne.symm, hd]
  have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset α)) => hlocal v)
  simp only [Finset.sum_add_distrib] at hh
  rw [hinside, ← hcross, G.sum_degrees_eq_twice_card_edges] at hh
  change (∑ i : κ, n i * (n i - 1)) + 2 * (∑ v : α, (out v).card) ≤ _
  omega
