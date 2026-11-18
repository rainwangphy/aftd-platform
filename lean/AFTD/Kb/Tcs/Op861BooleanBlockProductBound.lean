import AFTD.Prelude
import AFTD.Kb.Tcs.Op861BooleanRestrictionsInjective

/-!
# op861_boolean_block_product_bound

Topic: graphs   Node: 7a21b45d34df

Provenance: helper lemma. Finite product bound used for op861_disjoint_boolean_windows_count.

For Boolean assignments on a finite coordinate set and any family of block predicates depending on the assignment outside all blocks, the number of assignments satisfying every predicate is at most the sum over outside assignments of the product of the numbers of allowed assignments on the individual blocks. Blocks may overlap.
-/

open scoped BigOperators

theorem op861_boolean_block_product_bound (β ι : Type) [Fintype β] [DecidableEq β]
    [DecidableEq ι] (J : Finset ι) (B : ι → Finset β)
    (P : ({t : β // t ∉ J.biUnion B} → Bool) →
      ∀ i : {i : ι // i ∈ J}, ({t : β // t ∈ B i.1} → Bool) → Prop)
    [∀ a i v, Decidable (P a i v)] :
    ((Finset.univ : Finset (β → Bool)).filter (fun ω =>
      ∀ i : {i : ι // i ∈ J},
        P (fun t => ω t.1) i (fun t => ω t.1))).card ≤
      ∑ a : ({t : β // t ∉ J.biUnion B} → Bool),
        ∏ i : {i : ι // i ∈ J},
          ((Finset.univ : Finset ({t : β // t ∈ B i.1} → Bool)).filter (P a i)).card := by
  classical
  let O := {t : β // t ∉ J.biUnion B}
  let I := {i : ι // i ∈ J}
  let Block : I → Type := fun i => {t : β // t ∈ B i.1}
  let Good := {ω : β → Bool // ∀ i : I, P (fun t => ω t.1) i (fun t => ω t.1)}
  let Target := Σ a : O → Bool, ∀ i : I, {v : Block i → Bool // P a i v}
  let embed : Good → Target := fun ω =>
    ⟨fun t => ω.1 t.1, fun i => ⟨fun t => ω.1 t.1, ω.2 i⟩⟩
  let forget : Target → (O → Bool) × (∀ i : I, Block i → Bool) := fun z =>
    (z.1, fun i => (z.2 i).1)
  have hinj : Function.Injective embed := by
    intro a b h
    apply Subtype.ext
    apply op861_boolean_restrictions_injective β ι J B
    exact congrArg forget h
  have hcard := Fintype.card_le_of_injective embed hinj
  simpa [Good, Target, O, I, Block, Fintype.card_sigma, Fintype.card_pi, Fintype.card_subtype] using hcard
