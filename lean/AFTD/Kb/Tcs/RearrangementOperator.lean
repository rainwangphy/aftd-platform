import AFTD.Prelude
import AFTD.Kb.Tcs.Arr

/-!
# rearrangement_operator

Topic: combinatorics   Node: e33493553e66

Provenance: formalization of a published result. Source: arXiv:2611.05397, Section 2.2, Definition 2: Ranking and Unranking Permutations in Heap's Order

For a permutation $P \in \mathrm{Equiv.Perm}(\mathrm{Fin}\,m)$, the rearrangement operator $\widehat{P}$ acts on an array $A : \mathrm{Fin}\,m \to \mathrm{Fin}\,m$ under the source-index convention by $\widehat{P}(A) = A \circ P$.
-/

/-- The rearrangement operator associated to a permutation acting on an array under the source-index convention. -/
def rearrangement_operator {m : ℕ} (P : Equiv.Perm (Fin m)) (A : Arr m) : Arr m := A ∘ P
