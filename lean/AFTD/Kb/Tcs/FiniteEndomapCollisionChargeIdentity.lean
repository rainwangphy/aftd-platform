import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteEndomapMissingImageEqNonrepresentatives
import AFTD.Kb.Tcs.FiniteFunctionCollisionHeadPairInjective

/-!
# finite_endomap_collision_charge_identity

Topic: combinatorics   Node: 58b597d6333f

Provenance: helper lemma. Fiber-collision charge counting for the small-overlap good-center route to OP-110.

For a finite endomap whose fibers share a tail and whose elements are determined by tail and head, the number of missing image elements is the sum, over charged unordered head pairs, of the number of different tails charging each pair.
-/

theorem finite_endomap_collision_charge_identity
    (α β γ : Type) [Fintype α] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f r : α → α) (tail : α → β) (head : α → γ) (S : Finset (Sym2 γ))
    (hr : ∀ x, f (r (f x)) = f x)
    (htail : ∀ x y, f x = f y → tail x = tail y)
    (hkey : Function.Injective (fun x => (tail x, head x)))
    (hcover : ∀ x, r (f x) ≠ x → s(head x, head (r (f x))) ∈ S) :
    ((Finset.univ : Finset α) \ Finset.univ.image f).card =
      ∑ e ∈ S, (((Finset.univ.filter fun x => r (f x) ≠ x).filter fun x =>
        s(head x, head (r (f x))) = e).image tail).card := by
  rw [finite_endomap_missing_image_eq_nonrepresentatives α f r hr]
  let N : Finset α := Finset.univ.filter fun x => r (f x) ≠ x
  let E : α → Sym2 γ := fun x => s(head x, head (r (f x)))
  have hmaps : Set.MapsTo E (↑N) (↑S) := by
    intro x hx
    simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hcover x hx
  have hfiber := @Finset.card_eq_sum_card_fiberwise _ _ _ E N S hmaps
  have hinj_pair : Set.InjOn (fun x => (tail x, E x)) {x | r (f x) ≠ x} :=
    finite_function_collision_head_pair_injective α α β γ f r tail head hr htail hkey
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro e he
  have hinj : Set.InjOn tail (↑(N.filter fun x => E x = e)) := by
    intro x hx y hy htail_eq
    simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply hinj_pair hx.1 hy.1
    exact Prod.ext htail_eq (hx.2.trans hy.2.symm)
  rw [Finset.card_image_of_injOn hinj]
