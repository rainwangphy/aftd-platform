import AFTD.Prelude
import AFTD.Kb.Tcs.Arr
import AFTD.Kb.Tcs.RearrangementOperator
import AFTD.Kb.Tcs.RearrangementOperatorApply

/-!
# rearrangement_operator_comp_apply

Topic: combinatorics   Node: 241aaa774e8c

Provenance: helper lemma. arXiv:2611.05397, Section 2.2, Lemma 1: Ranking and Unranking Permutations in Heap's Order

For any array $A$ of order $m$, index $i \in \mathrm{Fin}\,m$, and permutations $P, Q \in \mathrm{Equiv.Perm}(\mathrm{Fin}\,m)$, applying the composition of rearrangement operators $(\widehat{P} \circ \widehat{Q})(A)$ at index $i$ yields $\widehat{Q \circ P}(A)[i] = A(Q(P(i)))$.
-/

/-- Pointwise composition of rearrangement operators: $(\widehat{P} \circ \widehat{Q})(A)[i] = \widehat{Q \circ P}(A)[i]$. -/
theorem rearrangement_operator_comp_apply {m : ℕ} (P Q : Equiv.Perm (Fin m)) (A : Arr m) (i : Fin m) :
    (rearrangement_operator P ∘ rearrangement_operator Q) A i = rearrangement_operator (Q * P) A i := by
  rfl
