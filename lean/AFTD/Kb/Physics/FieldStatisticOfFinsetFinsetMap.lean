import AFTD.Prelude
import AFTD.Kb.Physics.FieldStatistic
import AFTD.Kb.Physics.FieldStatisticOfFinset
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
import AFTD.Kb.Physics.FieldStatisticInstCommGroup
import AFTD.Kb.Physics.FieldStatisticInstFintype
import AFTD.Kb.Physics.FieldStatisticInstAddMonoid
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# FieldStatistic.ofFinset_finset_map

Topic: quantum_field_theory   Node: f475a984c0dd

Provenance: formalization of a published result. Source: Physlib, `FieldStatistic.ofFinset_finset_map`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/FieldStatistics/OfFinset.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

FieldStatistic.ofFinset_finset_map
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open FieldStatistic in
variable {𝓕 : Type} in
lemma FieldStatistic.ofFinset_finset_map {n m : ℕ}
    (q : 𝓕 → FieldStatistic) (i : Fin m → Fin n) (hi : Function.Injective i)
    (f : Fin n → 𝓕) (a : Finset (Fin m)) :
    ofFinset q (f ∘ i) a = ofFinset q f (a.map ⟨i, hi⟩) := by
  simp only [ofFinset]
  apply FieldStatistic.ofList_perm
  rw [← List.map_map]
  refine List.Perm.map f ?_
  apply List.perm_of_nodup_nodup_toFinset_eq
  · refine (List.nodup_map_iff_inj_on ?_).mpr ?_
    exact a.sort_nodup (fun x1 x2 => x1 ≤ x2)
    simp only [Finset.mem_sort]
    intro x hx y hy
    exact fun a => hi a
  · exact (Finset.map { toFun := i, inj' := hi } a).sort_nodup (fun x1 x2 => x1 ≤ x2)
  · ext a
    simp
