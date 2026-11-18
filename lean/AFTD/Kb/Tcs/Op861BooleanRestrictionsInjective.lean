import AFTD.Prelude

/-!
# op861_boolean_restrictions_injective

Topic: graphs   Node: 289e7a040c39

Provenance: helper lemma. Finite restriction injection used in op861_disjoint_boolean_windows_count.

A Boolean function on a finite set is determined by its restrictions to the complement of a union of blocks and to each block in the indexed family.
-/

open scoped BigOperators

theorem op861_boolean_restrictions_injective (β ι : Type) [Fintype β]
    [DecidableEq β] [DecidableEq ι] (J : Finset ι) (B : ι → Finset β) :
    Function.Injective (fun ω : β → Bool =>
      ((fun t : {t : β // t ∉ J.biUnion B} => ω t.1),
       (fun i : {i : ι // i ∈ J} => fun t : {t : β // t ∈ B i.1} => ω t.1))) := by
  classical
  intro f g h
  funext t
  by_cases ht : t ∈ J.biUnion B
  · obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    have hh := congrArg Prod.snd h
    have hi' := congrFun hh ⟨i, hi⟩
    exact congrFun hi' ⟨t, hti⟩
  · have hh := congrArg Prod.fst h
    exact congrFun hh ⟨t, ht⟩
