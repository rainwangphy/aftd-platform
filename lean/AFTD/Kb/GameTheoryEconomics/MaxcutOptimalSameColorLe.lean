import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_optimal_same_color_le

Topic: equilibria   Node: e4096ae1dd2c

Provenance: helper lemma. step towards maxcut_optimal_strong_of_degree_le (arXiv:2610.04948, Corollary 9)

At an optimal coloring σ of the Max-k-Cut game, for every vertex v and every color c, the number of neighbours of v with color σ(v) is at most the number of neighbours with color c (optimal colorings are Nash equilibria).
-/

theorem maxcut_optimal_same_color_le {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (hopt : is_maxcut_optimal G σ) (v : V)
    (c : Fin k) :
    (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card := by
  classical
  set τ := Function.update σ v c with hτ
  have hS := maxcut_welfare_split G σ {v}
  have hT := maxcut_welfare_split G τ {v}
  have hC : ∑ x ∈ ({v} : Finset V)ᶜ, ∑ w ∈ ({v} : Finset V)ᶜ,
      (if G.Adj x w ∧ τ w ≠ τ x then 1 else 0 : ℕ) =
      ∑ x ∈ ({v} : Finset V)ᶜ, ∑ w ∈ ({v} : Finset V)ᶜ,
      (if G.Adj x w ∧ σ w ≠ σ x then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun w hw => ?_
    have hx' : x ≠ v := by simpa using hx
    have hw' : w ≠ v := by simpa using hw
    simp [hτ, Function.update_of_ne hx', Function.update_of_ne hw']
  have hUS := maxcut_utility_sum_split G σ {v}
  have hUT := maxcut_utility_sum_split G τ {v}
  simp only [Finset.sum_singleton, SimpleGraph.irrefl, false_and, if_false] at hS hT hUS hUT
  have hle : maxcut_utility G τ v ≤ maxcut_utility G σ v := by
    have := hopt τ; omega
  have hτu : maxcut_utility G τ v =
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w ≠ c).card := by
    unfold maxcut_utility
    congr 1
    refine Finset.filter_congr fun w _ => ?_
    by_cases hw : w = v
    · subst hw; simp
    · simp [hτ, Function.update_of_ne hw]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun w => G.Adj v w) (fun w => σ w = σ v)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun w => G.Adj v w) (fun w => σ w = c)
  simp only [Finset.filter_filter] at h1 h2
  rw [hτu] at hle
  unfold maxcut_utility at hle
  simp only [ne_eq] at hle h1 h2
  omega
