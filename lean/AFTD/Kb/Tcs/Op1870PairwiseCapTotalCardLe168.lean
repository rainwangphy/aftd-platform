import AFTD.Prelude
import AFTD.Kb.Tcs.Op1870PairwiseCapCardIdentity

/-!
# op_1870_pairwise_cap_total_card_le_168

Topic: combinatorics   Node: 6b0368bb2631

Provenance: helper lemma. arXiv:2611.19543 Section 4

For any three mutually disjoint finsets $A_0, A_1, A_2 \subseteq \mathbb{F}_3^6$, if each pairwise union $A_0 \cup A_1$, $A_0 \cup A_2$, and $A_1 \cup A_2$ has cardinality at most 112, then their total cardinality satisfies $|A_0| + |A_1| + |A_2| \le 168$.
-/

/-- Total cardinality of three pairwise disjoint sets in dimension 6 is at most 168 if each pairwise union has size at most 112. -/
theorem op_1870_pairwise_cap_total_card_le_168
    (A₀ A₁ A₂ : Finset (Fin 6 → ZMod 3))
    (h01 : Disjoint A₀ A₁) (h02 : Disjoint A₀ A₂) (h12 : Disjoint A₁ A₂)
    (hC01 : (A₀ ∪ A₁).card ≤ 112)
    (hC02 : (A₀ ∪ A₂).card ≤ 112)
    (hC12 : (A₁ ∪ A₂).card ≤ 112) :
    A₀.card + A₁.card + A₂.card ≤ 168 := by
  have h := op_1870_pairwise_cap_card_identity A₀ A₁ A₂ h01 h02 h12
  omega
