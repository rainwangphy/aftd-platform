import AFTD.Prelude
import AFTD.Kb.Tcs.McdoMaximalChain

/-!
# mcdo_diamond_move

Topic: combinatorics   Node: aa842c5f32ff

Provenance: formalization of a published result. Source: arXiv:2611.26888 (structure of linear extensions of posets and lexicographic shellings), Section 2.2 (diamond moves, before Definition 2.2).

Diamond move with respect to the labelling by k : P → Fin |P| (the edge labelling λ_k of J(P) gives the cover I ⋖ I ∪ {x} the label k x). For maximal chains m, m' of J(P) (elements of the subtype mcdo_maximal_chain P, functions Fin |P| → P), mcdo_diamond_move k m m' holds if there is a natural number i with i + 1 < |P| such that m'.1 = m.1 ∘ Equiv.swap ⟨i⟩ ⟨i+1⟩ (m' adds the elements at positions i and i+1 of m in the opposite order, all other ideals of the two chains being equal) and k (m.1 ⟨i⟩) < k (m.1 ⟨i+1⟩), i.e. m is the ascending one of the two maximal chains of the interval [I_i, I_{i+2}].
-/

def mcdo_diamond_move {P : Type*} [PartialOrder P] [Fintype P]
    (k : P → Fin (Fintype.card P)) (m m' : mcdo_maximal_chain P) : Prop :=
  ∃ (i : ℕ) (h : i + 1 < Fintype.card P),
    m'.1 = m.1 ∘ Equiv.swap (⟨i, by omega⟩ : Fin (Fintype.card P)) ⟨i + 1, h⟩ ∧
    k (m.1 ⟨i, by omega⟩) < k (m.1 ⟨i + 1, h⟩)
