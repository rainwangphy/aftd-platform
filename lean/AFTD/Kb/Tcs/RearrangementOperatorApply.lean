import AFTD.Prelude
import AFTD.Kb.Tcs.Arr
import AFTD.Kb.Tcs.RearrangementOperator

/-!
# rearrangement_operator_apply

Topic: combinatorics   Node: d77fe755933b

Provenance: helper lemma. arXiv:2611.05397, Section 2.2, Definition 2: Ranking and Unranking Permutations in Heap's Order

Under the source-index convention, the entry at index $i$ of the rearranged array $\widehat{P}(A)$ equals $A(P(i))$ for any permutation $P$, array $A$, and index $i$.
-/

/-- Pointwise evaluation of the rearrangement operator under the source-index convention. -/
theorem rearrangement_operator_apply {m : ℕ} (P : Equiv.Perm (Fin m)) (A : Arr m) (i : Fin m) :
    rearrangement_operator P A i = A (P i) := by rfl
