import AFTD.Prelude

/-!
# op_1870_pairwise_cap_dim_one_exists

Topic: combinatorics   Node: 97da31a63ad4

Provenance: helper lemma. arXiv:2611.19543 Lemma 4

In dimension 1, there exist three mutually disjoint finsets $A_0, A_1, A_2 \subseteq \mathbb{F}_3^1$ such that each pairwise union $A_0 \cup A_1$, $A_0 \cup A_2$, and $A_1 \cup A_2$ is 3AP-free, and their total cardinality $|A_0| + |A_1| + |A_2| = 3$.
-/

/-- In dimension one, there exist three mutually disjoint sets whose pairwise unions are 3AP-free with total cardinality 3. -/
theorem op_1870_pairwise_cap_dim_one_exists :
    ∃ (A₀ A₁ A₂ : Finset (Fin 1 → ZMod 3)),
      Disjoint A₀ A₁ ∧
      Disjoint A₀ A₂ ∧
      Disjoint A₁ A₂ ∧
      ThreeAPFree (((A₀ ∪ A₁ : Finset _) : Set (Fin 1 → ZMod 3))) ∧
      ThreeAPFree (((A₀ ∪ A₂ : Finset _) : Set (Fin 1 → ZMod 3))) ∧
      ThreeAPFree (((A₁ ∪ A₂ : Finset _) : Set (Fin 1 → ZMod 3))) ∧
      A₀.card + A₁.card + A₂.card = 3 := by
  decide
