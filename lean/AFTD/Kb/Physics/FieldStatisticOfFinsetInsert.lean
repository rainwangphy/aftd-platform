import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticOfFinset
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticOfList
import AFTD.Kb.Physics.FieldStatisticOfListConsEqMul
import AFTD.Kb.Physics.FieldStatisticOfListPerm
import AFTD.Kb.Physics.FieldStatisticBosonicMulBosonic
import AFTD.Kb.Physics.FieldStatisticBosonicMulFermionic
import AFTD.Kb.Physics.FieldStatisticFermionicMulBosonic
import AFTD.Kb.Physics.FieldStatisticFermionicMulFermionic
import AFTD.Kb.Physics.FieldStatisticMulBosonic
import AFTD.Kb.Physics.FieldStatisticMulSelf
import AFTD.Kb.Physics.FieldStatisticFermionicNotEqBonsic
import AFTD.Kb.Physics.FieldStatisticNeqFermionicIffEqBosonic
import AFTD.Kb.Physics.FieldStatisticNeqBosonicIffEqFermionic
import AFTD.Kb.Physics.FieldStatisticBosonicNeIffFermionicEq
import AFTD.Kb.Physics.FieldStatisticFermionicNeIffBosonicEq
import AFTD.Kb.Physics.FieldStatisticOfListSingleton
import AFTD.Kb.Physics.FieldStatisticOfListFreeMonoid
import AFTD.Kb.Physics.FieldStatisticOfListEmpty
import AFTD.Kb.Physics.FieldStatisticOfListAppend
import AFTD.Kb.Physics.FieldStatisticOfListInsertionSort
import AFTD.Kb.Physics.FieldStatisticAddEqMul
import AFTD.Kb.Physics.FieldStatisticOfFinsetEmpty
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.PhyslibListInsertIdxGetElemFin
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.PhyslibListMemEraseIdxNodup

/-!
# FieldStatistic.ofFinset_insert

Topic: quantum_field_theory   Node: a293b345ac8e

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.ofFinset_insert`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/OfFinset.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.ofFinset_insert
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
lemma FieldStatistic.ofFinset_insert (q : 𝓕 → FieldStatistic) (φs : List 𝓕) (a : Finset (Fin φs.length))
    (i : Fin φs.length) (h : i ∉ a) :
    ofFinset q φs.get (Insert.insert i a) = (q φs[i]) * ofFinset q φs.get a := by
  simp only [ofFinset, Fin.getElem_fin]
  rw [← ofList_cons_eq_mul]
  have h1 : (φs[↑i] :: List.map φs.get (a.sort (fun x1 x2 => x1 ≤ x2)))
      = List.map φs.get (i :: a.sort (fun x1 x2 => x1 ≤ x2)) := by
      simp
  erw [h1]
  apply ofList_perm
  refine List.Perm.map φs.get ?_
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact (Insert.insert i a).sort_nodup (fun x1 x2 => x1 ≤ x2)
  · simp only [List.nodup_cons, Finset.mem_sort, Finset.sort_nodup, and_true]
    exact h
  intro a
  simp
