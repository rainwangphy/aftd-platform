import AFTD.Prelude
import AFTD.Kb.Tcs.PosetSortingMap
import AFTD.Kb.Tcs.IsBraidIso
import AFTD.Kb.Tcs.PosetSortingMapIntertwineIff

/-!
# poset_sorting_map_braid_iso_iff

Topic: combinatorics   Node: ee3ee6261ea7

Provenance: helper lemma. Step of arXiv:2611.15540, Theorem A (Theorem 2.1 and Corollary 2.2)

For partially ordered sets P and Q, the solutions (P,R_P) and (Q,R_Q) are isomorphic iff P and Q are order isomorphic.
-/

theorem poset_sorting_map_braid_iso_iff (P Q : Type*) [PartialOrder P] [PartialOrder Q] :
    is_braid_iso (poset_sorting_map P) (poset_sorting_map Q) ↔ Nonempty (P ≃o Q) := by
  constructor
  · rintro ⟨e, he⟩
    have hlt := (poset_sorting_map_intertwine_iff e).1 he
    refine ⟨⟨e, fun {a b} => ?_⟩⟩
    simp only [le_iff_lt_or_eq, hlt, e.injective.eq_iff]
  · rintro ⟨f⟩
    exact ⟨f.toEquiv, (poset_sorting_map_intertwine_iff f.toEquiv).2 fun x y => f.lt_iff_lt⟩
