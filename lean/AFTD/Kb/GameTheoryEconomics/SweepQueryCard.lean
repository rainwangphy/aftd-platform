import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SweepQuery
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# sweep_query_card

Topic: combinatorial_games   Node: 39b808aa0b61

Provenance: helper lemma. arXiv:2611.01281 Section 5

For all natural numbers M, N, r, and j with r + 1 < M and j < N, the cardinality of the sweep query satisfies (sweep_query M N r j).card = N + 1.
-/

/-- The cardinality of the sweep query T_{r,j} is N + 1. -/
theorem sweep_query_card (M N : ℕ) (r j : ℕ) (hr : r + 1 < M) (hj : j < N) :
    (sweep_query M N r j).card = N + 1 := by
  have hrM : r < M := Nat.lt_of_succ_lt hr
  let a : Fin M := ⟨r, hrM⟩
  let b : Fin M := ⟨r + 1, hr⟩
  let c : Fin N := ⟨j, hj⟩
  have hset : sweep_query M N r j =
      ({a} : Finset (Fin M)) ×ˢ (Finset.Ici c) ∪ ({b} : Finset (Fin M)) ×ˢ (Finset.Iic c) := by
    ext p
    simp only [sweep_query, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, Finset.mem_singleton, Finset.mem_Ici, Finset.mem_Iic,
      a, b, c, Fin.le_def, Fin.ext_iff]
  rw [hset]
  have hdisj : Disjoint (({a} : Finset (Fin M)) ×ˢ (Finset.Ici c))
      (({b} : Finset (Fin M)) ×ˢ (Finset.Iic c)) := by
    rw [Finset.disjoint_product]
    left
    rw [Finset.disjoint_singleton]
    simp [a, b]
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Finset.card_singleton, Fin.card_Ici, Fin.card_Iic]
  simp
  omega
