import AFTD.Prelude
import AFTD.Kb.Tcs.Arr
import AFTD.Kb.Tcs.RearrangementOperator

/-!
# rearrangement_operator_anti_homomorphism

Topic: combinatorics   Node: 4c697ad2110d

Provenance: formalization of a published result. Source: arXiv:2611.05397, Section 2.2, Lemma 1: Ranking and Unranking Permutations in Heap's Order

Under the source-index convention where the rearrangement operator $\widehat{P}$ acts on an array $A : \mathrm{Fin}\,m \to \mathrm{Fin}\,m$ by $\widehat{P}(A) = A \circ P$, the composition of rearrangement operators satisfies the anti-homomorphism property $\widehat{P} \circ \widehat{Q} = \widehat{Q \circ P}$ for all permutations $P, Q \in \mathrm{Equiv.Perm}(\mathrm{Fin}\,m)$.
-/

/-- Operator anti-homomorphism under the source-index convention: $\widehat{P} \circ \widehat{Q} = \widehat{Q \circ P}$. -/
theorem rearrangement_operator_anti_homomorphism (m : ℕ) (P Q : Equiv.Perm (Fin m)) :
    rearrangement_operator P ∘ rearrangement_operator Q = rearrangement_operator (Q * P) := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
