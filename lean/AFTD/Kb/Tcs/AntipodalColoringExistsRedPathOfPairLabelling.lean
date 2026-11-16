import AFTD.Prelude
import AFTD.Kb.Tcs.HypercubeGraph
import AFTD.Kb.Tcs.HypercubeAntipode
import AFTD.Kb.Tcs.IsAntipodalColoring
import AFTD.Kb.Tcs.HypercubeRedSubgraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# antipodal_coloring_exists_red_path_of_pair_labelling

Topic: combinatorics   Node: 4495ae546b0e

Provenance: helper lemma. arXiv:2611.16243, Sections 2-3 (proof of Theorem 1.1)

Conditional form of the antipodal-coloring theorem: if for every K ≥ 2 there is no labelling of the vertices of Q_K by ordered pairs of distinct elements of Fin K that swaps under the antipode and in which adjacent vertices share the first or the second entry (the statement antipodal_pair_labelling_impossible), then for every n ≥ 2 and every antipodal edge coloring c of hypercube_graph n some vertex y is joined to hypercube_antipode y by a path in hypercube_red_subgraph n c.
-/

theorem antipodal_coloring_exists_red_path_of_pair_labelling
    (hcore : ∀ K : ℕ, 2 ≤ K → ¬ ∃ q : (Fin K → Bool) → Fin K × Fin K,
      (∀ x, (q x).1 ≠ (q x).2) ∧
      (∀ x, q (hypercube_antipode x) = ((q x).2, (q x).1)) ∧
      (∀ x y, (hypercube_graph K).Adj x y → (q x).1 = (q y).1 ∨ (q x).2 = (q y).2))
    (n : ℕ) (hn : 2 ≤ n) (c : (hypercube_graph n).edgeSet → Bool)
    (hc : is_antipodal_coloring n c) :
    ∃ (y : Fin n → Bool) (p : (hypercube_red_subgraph n c).Walk y (hypercube_antipode y)),
      p.IsPath := by
  classical
  by_contra hno
  push Not at hno
  set G := hypercube_red_subgraph n c with hG
  set K := n + Fintype.card (Fin n → Bool) with hK
  have hnK : n ≤ K := Nat.le_add_right _ _
  have hmK : Fintype.card (Fin n → Bool) ≤ K := Nat.le_add_left _ _
  -- labels of red components
  let e := Fintype.equivFin (Fin n → Bool)
  let p : (Fin n → Bool) → Fin K := fun y =>
    Fin.castLE hmK (e (Quot.out (G.connectedComponentMk y)))
  have hp : ∀ y z, p y = p z ↔ G.Reachable y z := by
    intro y z
    constructor
    · intro h
      have h1 : e (Quot.out (G.connectedComponentMk y)) = e (Quot.out (G.connectedComponentMk z)) :=
        Fin.castLE_injective hmK h
      have h2 := e.injective h1
      have h3 : G.connectedComponentMk y = G.connectedComponentMk z := by
        have a := Quot.out_eq (G.connectedComponentMk y)
        have b := Quot.out_eq (G.connectedComponentMk z)
        rw [h2] at a
        exact a.symm.trans b
      exact SimpleGraph.ConnectedComponent.eq.mp h3
    · intro h
      have h3 : G.connectedComponentMk y = G.connectedComponentMk z :=
        SimpleGraph.ConnectedComponent.eq.mpr h
      simp only [p, h3]
  have hanti : ∀ {m : ℕ} (y : Fin m → Bool), hypercube_antipode (hypercube_antipode y) = y := by
    intro m y; funext i; simp [hypercube_antipode]
  have hnotreach : ∀ y, ¬ G.Reachable y (hypercube_antipode y) := by
    intro y ⟨w⟩
    exact hno y w.toPath.1 w.toPath.2
  let π : (Fin K → Bool) → (Fin n → Bool) := fun x i => x (Fin.castLE hnK i)
  have hπanti : ∀ x, π (hypercube_antipode x) = hypercube_antipode (π x) := by
    intro x; rfl
  have hdist_anti : ∀ {m : ℕ} (y z : Fin m → Bool),
      hammingDist (hypercube_antipode y) (hypercube_antipode z) = hammingDist y z := by
    intro m y z
    simp [hammingDist, hypercube_antipode]
  have hπdist : ∀ x x' : Fin K → Bool, hammingDist (π x) (π x') ≤ hammingDist x x' := by
    intro x x'
    unfold hammingDist
    refine Finset.card_le_card_of_injOn (fun i => Fin.castLE hnK i) ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
      exact hi
    · intro i _ j _ hij
      exact Fin.castLE_injective hnK hij
  let q : (Fin K → Bool) → Fin K × Fin K := fun x => (p (π x), p (hypercube_antipode (π x)))
  apply hcore K (by omega)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x h
    exact hnotreach _ ((hp _ _).mp h)
  · intro x
    simp only [q, hπanti, hanti]
  · intro x x' hadj
    have hd : hammingDist (π x) (π x') ≤ 1 := by
      have := hπdist x x'
      have h1 : hammingDist x x' = 1 := hadj
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with h0 | h1
    · left
      show p (π x) = p (π x')
      rw [hammingDist_eq_zero.mp h0]
    · have hA : (hypercube_graph n).Adj (π x) (π x') := h1
      have hA' : (hypercube_graph n).Adj (hypercube_antipode (π x)) (hypercube_antipode (π x')) := by
        show hammingDist _ _ = 1
        rw [hdist_anti]; exact h1
      cases hcol : c ⟨s(π x, π x'), hA⟩
      · right
        have hc' := hc (π x) (π x') hA hA'
        rw [hcol] at hc'
        have hred : G.Adj (hypercube_antipode (π x)) (hypercube_antipode (π x')) :=
          ⟨hA', by
            cases h2 : c ⟨s(hypercube_antipode (π x), hypercube_antipode (π x')), hA'⟩
            · rw [h2] at hc'; simp at hc'
            · rfl⟩
        exact (hp _ _).mpr hred.reachable
      · left
        have hred : G.Adj (π x) (π x') := ⟨hA, hcol⟩
        exact (hp _ _).mpr hred.reachable
