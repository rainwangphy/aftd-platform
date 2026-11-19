import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph

/-!
# three_token_cycle_five_indep_num

Topic: graphs   Node: 586f6d5a1ff6

Provenance: formalization of a published result. Source: arXiv:2611.22830 Section 5 -- Independent sets in the 2-token graph of a cycle and kings on the torus

The independence number of the 3-token graph of the cycle graph C_5 on 5 vertices equals 5.
-/

private instance three_token_cycle_five_indep_num_inst :
    DecidableRel (token_graph (SimpleGraph.cycleGraph 5) 3).Adj :=
  fun x y => decidable_of_iff (∃ u v : Fin 5, (SimpleGraph.cycleGraph 5).Adj u v ∧
      symmDiff (x.val : Finset (Fin 5)) (y.val : Finset (Fin 5)) = {u, v}) Iff.rfl

/-- Index of the matched edge (of a fixed perfect matching of the ten 3-subsets of `Fin 5`)
containing a 3-subset. -/
private def three_token_cycle_five_indep_num_idx (s : Finset (Fin 5)) : Fin 5 :=
  if s = {0,1,2} ∨ s = {0,1,3} then 0
  else if s = {0,1,4} ∨ s = {0,2,4} then 1
  else if s = {1,2,3} ∨ s = {1,2,4} then 2
  else if s = {0,2,3} ∨ s = {2,3,4} then 3
  else if s = {0,3,4} ∨ s = {1,3,4} then 4
  else 0

/-- The five consecutive triples of the 5-cycle, an independent set in `F_3(C_5)`. -/
private def three_token_cycle_five_indep_num_set : Finset {s : Finset (Fin 5) // s.card = 3} :=
  {⟨{0,1,2}, by decide⟩, ⟨{1,2,3}, by decide⟩, ⟨{2,3,4}, by decide⟩,
   ⟨{0,3,4}, by decide⟩, ⟨{0,1,4}, by decide⟩}

/-- If `f` is constant on the edges of a matching covering all vertices, an independent set
injects into `Fin n` along `f`, hence has at most `n` vertices. -/
private lemma three_token_cycle_five_indep_num_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {n : ℕ} (f : α → Fin n)
    (h : ∀ x y, x ≠ y → f x = f y → G.Adj x y)
    {t : Finset α} (ht : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ G.Adj x y) : t.card ≤ n := by
  have hinj : Set.InjOn f ↑t := by
    intro x hx y hy hxy
    by_contra hne
    exact ht x hx y hy hne (h x y hne hxy)
  have h1 : (t.image f).card = t.card := Finset.card_image_of_injOn hinj
  have h2 : (t.image f).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
  rw [Fintype.card_fin] at h2
  omega

/-- The five consecutive triples form an independent set in the 3-token graph of `C_5`. -/
private lemma three_token_cycle_five_indep_num_indep :
    (token_graph (SimpleGraph.cycleGraph 5) 3).IsIndepSet ↑three_token_cycle_five_indep_num_set := by
  rw [SimpleGraph.isIndepSet_iff]
  decide

/-- The explicit independent set has five elements. -/
private lemma three_token_cycle_five_indep_num_set_card :
    three_token_cycle_five_indep_num_set.card = 5 := by decide

/-- No independent set of the 3-token graph of `C_5` is larger than the five consecutive triples. -/
private lemma three_token_cycle_five_indep_num_max (t : Finset {s : Finset (Fin 5) // s.card = 3})
    (ht : (token_graph (SimpleGraph.cycleGraph 5) 3).IsIndepSet ↑t) :
    t.card ≤ three_token_cycle_five_indep_num_set.card := by
  have hp : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ (token_graph (SimpleGraph.cycleGraph 5) 3).Adj x y := by
    have h1 := (SimpleGraph.isIndepSet_iff (G := token_graph (SimpleGraph.cycleGraph 5) 3)
      (s := ↑t)).mp ht
    simpa [Set.Pairwise] using h1
  have hkey : ∀ x y : {s : Finset (Fin 5) // s.card = 3}, x ≠ y →
      three_token_cycle_five_indep_num_idx x.val = three_token_cycle_five_indep_num_idx y.val →
      (token_graph (SimpleGraph.cycleGraph 5) 3).Adj x y := by decide
  have h := three_token_cycle_five_indep_num_card_le (token_graph (SimpleGraph.cycleGraph 5) 3)
    (fun x : {s : Finset (Fin 5) // s.card = 3} => three_token_cycle_five_indep_num_idx x.val)
    hkey hp
  rw [three_token_cycle_five_indep_num_set_card]
  exact h

/-- The independence number of the 3-token graph of the 5-cycle is 5. -/
theorem three_token_cycle_five_indep_num :
    (token_graph (SimpleGraph.cycleGraph 5) 3).indepNum = 5 := by
  have h := SimpleGraph.maximumIndepSet_card_eq_indepNum (G := token_graph (SimpleGraph.cycleGraph 5) 3)
    three_token_cycle_five_indep_num_set
    ⟨three_token_cycle_five_indep_num_indep, three_token_cycle_five_indep_num_max⟩
  rw [three_token_cycle_five_indep_num_set_card] at h
  exact h.symm
