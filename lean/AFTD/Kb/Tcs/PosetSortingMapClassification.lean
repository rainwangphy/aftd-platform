import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMapIdempotentBraid
import AFTD.Kb.Tcs.BraidAutPosetSortingMap
import AFTD.Kb.Tcs.PosetSortingMapBraidIsoIff
import AFTD.Kb.Tcs.SwapIdempotentBraidIffPosetSortingMap
import AFTD.Kb.Tcs.IsBraidIso
import AFTD.Kb.Tcs.BraidAut
import AFTD.Kb.Tcs.IsBraidSolution
import AFTD.Kb.Tcs.PosetSortingMap

/-!
# poset_sorting_map_classification

Topic: combinatorics   Node: 47f68c8b15f8

Provenance: formalization of a published result. Source: arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2); Aut(P,R_P)=Aut(P) stated as: a permutation commutes with R_P iff it is an order automorphism

Let P and Q be partially ordered sets and X a set, and let R_P : P×P → P×P map (x,y) to (y,x) if y<x and fix it otherwise. Then (1) R_P satisfies the braid equation R12∘R23∘R12 = R23∘R12∘R23 and is idempotent; (2) a permutation of P commutes with R_P (i.e. lies in Aut(P,R_P)) iff it is an order automorphism of P; (3) there is a bijection P → Q intertwining R_P and R_Q iff P and Q are order isomorphic; (4) for every map R : X×X → X×X with R(x,y) ∈ {(x,y),(y,x)} for all x,y, R is an idempotent solution of the braid equation iff R = R_P for exactly one partial order on X.
-/

theorem poset_sorting_map_classification (P Q X : Type*) [PartialOrder P] [PartialOrder Q] :
    (is_braid_solution (poset_sorting_map P) ∧
        poset_sorting_map P ∘ poset_sorting_map P = poset_sorting_map P) ∧
      (∀ σ : Equiv.Perm P, σ ∈ braid_aut (poset_sorting_map P) ↔ ∃ f : P ≃o P, f.toEquiv = σ) ∧
      (is_braid_iso (poset_sorting_map P) (poset_sorting_map Q) ↔ Nonempty (P ≃o Q)) ∧
      (∀ R : X × X → X × X, (∀ x y : X, R (x, y) = (x, y) ∨ R (x, y) = (y, x)) →
        ((is_braid_solution R ∧ R ∘ R = R) ↔ ∃! o : PartialOrder X, R = @poset_sorting_map X o)) := by
  exact ⟨poset_sorting_map_idempotent_braid P, braid_aut_poset_sorting_map P,
    poset_sorting_map_braid_iso_iff P Q, fun R hR => swap_idempotent_braid_iff_poset_sorting_map R hR⟩
