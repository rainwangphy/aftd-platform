import AFTD.Prelude

/-!
# op874_one_sided_perfect_matching_crosses

Topic: graphs   Node: 66ccfb4e9f8b

Provenance: helper lemma. Structural two-port reduction for OP-874; experiments 43048, 43073 and 43075 test the local-state implications.

For two involutions on a finite set, if the first swaps a Boolean partition and the second sends every false vertex to a true vertex, then the second swaps the partition as well.
-/

theorem op874_one_sided_perfect_matching_crosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (flag : V → Bool) (mate other : V → V)
    (hmate : ∀ v, mate (mate v) = v)
    (hflip : ∀ v, flag (mate v) = !flag v)
    (hother : ∀ v, other (other v) = v)
    (hone : ∀ v, flag v = false → flag (other v) = true) :
    ∀ v, flag (other v) = !flag v := by
  classical
  let P := {v : V // flag v = true}
  let Q := {v : V // flag v = false}
  let eqv : Q ≃ P :=
    { toFun := fun q => ⟨mate q.1, by simp [hflip, q.2]⟩
      invFun := fun p => ⟨mate p.1, by simp [hflip, p.2]⟩
      left_inv := fun q => Subtype.ext (hmate q.1)
      right_inv := fun p => Subtype.ext (hmate p.1) }
  have hcard : Fintype.card Q = Fintype.card P := Fintype.card_congr eqv
  let f : Q → P := fun q => ⟨other q.1, hone q.1 q.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv : other x.1 = other y.1 := congrArg Subtype.val h
    have hh := congrArg other hv
    simpa [hother] using hh
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj,hcard⟩).2
  intro v
  cases hv : flag v with
  | false => simpa [hv] using hone v hv
  | true =>
    obtain ⟨q,hq⟩ := hsurj ⟨v,hv⟩
    have hvq : other q.1 = v := congrArg Subtype.val hq
    have hqv : other v = q.1 := by rw [←hvq, hother]
    simp [hv, hqv, q.2]
