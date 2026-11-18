import AFTD.Prelude
import AFTD.Kb.Tcs.Op861BooleanBlockProductBound

/-!
# op861_boolean_block_uniform_bound

Topic: graphs   Node: c13bc1b1a5de

Provenance: helper lemma. Finite independent-block count for op861_disjoint_boolean_windows_count.

A uniform bound on each block fiber yields a bound on the total number of good Boolean assignments by the outside-assignment count times the product of local bounds.
-/

open scoped BigOperators

theorem op861_boolean_block_uniform_bound (β ι : Type) [Fintype β] [DecidableEq β]
    [DecidableEq ι] (J : Finset ι) (B : ι → Finset β)
    (Good : (β → Bool) → Prop) [DecidablePred Good]
    (P : ({t : β // t ∉ J.biUnion B} → Bool) →
      ∀ i : {i : ι // i ∈ J}, ({t : β // t ∈ B i.1} → Bool) → Prop)
    [∀ a i v, Decidable (P a i v)] (limit : ι → ℕ)
    (hcover : ∀ ω, Good ω → ∀ i : {i : ι // i ∈ J},
      P (fun t => ω t.1) i (fun t => ω t.1))
    (hlocal : ∀ a i, ((Finset.univ : Finset ({t : β // t ∈ B i.1} → Bool)).filter
      (P a i)).card ≤ limit i.1) :
    ((Finset.univ : Finset (β → Bool)).filter Good).card ≤
      Fintype.card ({t : β // t ∉ J.biUnion B} → Bool) *
        ∏ i : {i : ι // i ∈ J}, limit i.1 := by
  classical
  let V : Finset (β → Bool) := Finset.univ.filter (fun ω =>
    ∀ i : {i : ι // i ∈ J}, P (fun t => ω t.1) i (fun t => ω t.1))
  have hsub : ((Finset.univ : Finset (β → Bool)).filter Good) ⊆ V := by
    intro ω hω
    dsimp [V]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hcover ω hω
  have hprod := op861_boolean_block_product_bound β ι J B P
  calc
    _ ≤ V.card := Finset.card_le_card hsub
    _ ≤ ∑ a : ({t : β // t ∉ J.biUnion B} → Bool),
        ∏ i : {i : ι // i ∈ J},
          ((Finset.univ : Finset ({t : β // t ∈ B i.1} → Bool)).filter (P a i)).card := by
      simpa [V] using hprod
    _ ≤ ∑ _a : ({t : β // t ∉ J.biUnion B} → Bool),
        ∏ i : {i : ι // i ∈ J}, limit i.1 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.prod_le_prod'
      intro i hi
      convert hlocal a i using 1 <;> congr 1 <;> ext x <;> simp
    _ = _ := by simp
