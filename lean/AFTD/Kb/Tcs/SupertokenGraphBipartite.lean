import AFTD.Prelude
import AFTD.Kb.Tcs.SupertokenGraph
import AFTD.Kb.Tcs.Order

/-!
# supertoken_graph_bipartite

Topic: graphs   Node: ad921c7f551e

Provenance: formalization of a published result. Source: arXiv:2611.06275 Theorem 2.5 -- On generalized k-token graphs with distinguishable tokens and a maximum capacity of s tokens per vertex

Let G be a finite bipartite simple graph on vertex type V with decidable equality (satisfying G.IsBipartite). Let s ≥ 1 and 1 ≤ k ≤ s * Fintype.card V. Then the supertoken graph supertoken_graph G k s is bipartite (satisfies SimpleGraph.IsBipartite).
-/

/-- Splitting the number of tokens of a configuration lying in `S` off at a single coordinate. -/
private lemma supertoken_graph_bipartite_count_split {V : Type*} (S : Set V) [DecidablePred (· ∈ S)]
    {k : ℕ} (x : Fin k → V) (i : Fin k) :
    (Finset.univ.filter (fun j => x j ∈ S)).card
      = (if x i ∈ S then 1 else 0) +
        ((Finset.univ.erase i).filter (fun j => x j ∈ S)).card := by
  conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i)]
  rw [Finset.filter_insert]
  by_cases hp : x i ∈ S
  · rw [if_pos hp, Finset.card_insert_of_notMem (by simp), if_pos hp]
    omega
  · simp [hp]

/-- If two configurations differ only at a coordinate `i` whose token crosses `S` in one direction,
then the total number of tokens lying in `S` over the two configurations is odd. -/
private lemma supertoken_graph_bipartite_count_odd {V : Type*} {k : ℕ} {S : Set V}
    [DecidablePred (· ∈ S)] (x y : Fin k → V) (i : Fin k) (hxy : ∀ j, j ≠ i → x j = y j)
    (h : (x i ∈ S ∧ y i ∉ S) ∨ (x i ∉ S ∧ y i ∈ S)) :
    Odd ((Finset.univ.filter (fun j => x j ∈ S)).card +
      (Finset.univ.filter (fun j => y j ∈ S)).card) := by
  have hx := supertoken_graph_bipartite_count_split S x i
  have hy := supertoken_graph_bipartite_count_split S y i
  have hrest : ((Finset.univ.erase i).filter (fun j => y j ∈ S)).card
      = ((Finset.univ.erase i).filter (fun j => x j ∈ S)).card := by
    congr 1
    apply Finset.filter_congr
    intro j hj
    rw [hxy j (Finset.ne_of_mem_erase hj)]
  rw [hx, hy, hrest]
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := h
  · rw [if_pos ha, if_neg hb]
    exact ⟨_, by ring⟩
  · rw [if_neg ha, if_pos hb]
    exact ⟨_, by ring⟩

/-- Theorem 2.5: If G is bipartite, then F^s_{k x 1}(G) is bipartite for every admissible k, s. -/
theorem supertoken_graph_bipartite {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (hG : G.IsBipartite)
    (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ s * Fintype.card V) :
    (supertoken_graph G k s).IsBipartite := by
  classical
  obtain ⟨S, T, hST⟩ := hG.exists_isBipartiteWith
  -- Parity colouring: the parity of the number of tokens on the part `S`.
  let cnt : (Fin k → V) → ℕ := fun x => (Finset.univ.filter (fun i => x i ∈ S)).card
  refine SimpleGraph.IsBipartiteWith.isBipartite (s := {x | Even (cnt x.1)})
    (t := {x | Odd (cnt x.1)}) ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact (Nat.not_even_iff_odd.mpr hx') hx
  · rintro x y ⟨i, hi, hxy⟩
    -- the unique moved token crosses the bipartition, so it lies in `S` on exactly one side
    have hm := hST.mem_of_adj hi
    have hmem : (x.1 i ∈ S ∧ y.1 i ∉ S) ∨ (x.1 i ∉ S ∧ y.1 i ∈ S) := by
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hm
      · exact Or.inl ⟨h1, Set.disjoint_right.mp hST.disjoint h2⟩
      · exact Or.inr ⟨Set.disjoint_right.mp hST.disjoint h1, h2⟩
    have hodd := supertoken_graph_bipartite_count_odd x.1 y.1 i hxy hmem
    have hn := Nat.odd_add.mp hodd
    by_cases hcx : Even (cnt x.1)
    · left
      refine ⟨hcx, ?_⟩
      have hno : ¬ Odd (cnt x.1) := fun h => (Nat.not_even_iff_odd.mpr h) hcx
      exact Nat.not_even_iff_odd.mp (fun h => hno (hn.mpr h))
    · right
      refine ⟨Nat.not_even_iff_odd.mp hcx, ?_⟩
      exact hn.mp (Nat.not_even_iff_odd.mp hcx)
