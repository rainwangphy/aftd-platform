import AFTD.Prelude

/-!
# projected_sets_card_le_of_zero_lift

Topic: combinatorics   Node: 83cc38e43fde

Provenance: helper lemma. Supporting cardinality lemma for OP-259, arXiv:2610.19965 Question 3.1, deep session IN-185; used in the proposed r=n=3 reduction.

For a homomorphism of additive groups, if each pair from X and Y with opposite images sums to zero upstairs, the sum of the two image cardinalities is at most the size of the target plus the number of unique fibers of X.
-/

theorem projected_sets_card_le_of_zero_lift
    {α β : Type*} [AddGroup α] [AddGroup β] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (f : α →+ β) (X Y : Finset α)
    (hzero : ∀ x ∈ X, ∀ y ∈ Y, f x + f y = 0 → x + y = 0) :
    (X.image f).card + (Y.image f).card ≤ Fintype.card β +
      ((X.image f).filter (fun g => ∀ x ∈ X, ∀ x' ∈ X,
        f x = g → f x' = g → x = x')).card := by
  let P := X.image f
  let Q := Y.image (fun y => -f y)
  let U := P.filter (fun g => ∀ x ∈ X, ∀ x' ∈ X,
    f x = g → f x' = g → x = x')
  have hi : P ∩ Q ⊆ U := by
    intro g hg
    obtain ⟨hgP, hgQ⟩ := Finset.mem_inter.mp hg
    obtain ⟨y, hy, hgy⟩ := Finset.mem_image.mp hgQ
    refine Finset.mem_filter.mpr ⟨hgP, ?_⟩
    intro x hx x' hx' hxg hxg'
    have hxy : x + y = 0 := hzero x hx y hy (by rw [hxg, ← hgy]; simp)
    have hx'y : x' + y = 0 := hzero x' hx' y hy (by rw [hxg', ← hgy]; simp)
    exact add_right_cancel (hxy.trans hx'y.symm)
  have hQ : Q.card = (Y.image f).card := by
    calc
      Q.card = ((Y.image f).image (fun y => -y)).card := by
        simp only [Q, Finset.image_image, Function.comp_def]
      _ = (Y.image f).card := Finset.card_image_of_injective _ neg_injective
  have hicard := Finset.card_le_card hi
  have hucard : (P ∪ Q).card ≤ Fintype.card β := Finset.card_le_univ _
  have heq := Finset.card_union_add_card_inter P Q
  change P.card + (Y.image f).card ≤ Fintype.card β + U.card
  omega
