import AFTD.Prelude
import AFTD.Kb.Tcs.WildInvolutionsConjugateOfFixedCount

/-!
# wild_normalized_array_single_color_isomorphism

Topic: graphs   Node: 52e5c286a0b3

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite involution conjugacy and permutation transport, supporting the moment route for https://arxiv.org/html/2610.22142v1. Background https://arxiv.org/abs/0911.3604 . No new wild-number bound or research advance is claimed.

For two symmetric idempotent row-injective arrays A and B on Fin n and any chosen colors a and b, there is a vertex permutation e sending a to b such that B(e x,e y)=b if and only if A(x,y)=a for every pair. This is a single-color isomorphism; it makes no simultaneous claim for two colors.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

theorem wild_normalized_array_single_color_isomorphism
    (n : ℕ) (A B : Fin n → Fin n → Fin n)
    (hAd : ∀ x, A x x = x) (hAs : ∀ x y, A x y = A y x)
    (hAi : ∀ x, Function.Injective (A x))
    (hBd : ∀ x, B x x = x) (hBs : ∀ x y, B x y = B y x)
    (hBi : ∀ x, Function.Injective (B x))
    (a b : Fin n) :
    ∃ e : Equiv.Perm (Fin n), e a = b ∧
      ∀ x y, B (e x) (e y) = b ↔ A x y = a := by
  classical
  let rowA : Fin n → Equiv.Perm (Fin n) := fun x =>
    Equiv.ofBijective (A x) ⟨hAi x, Finite.surjective_of_injective (hAi x)⟩
  let rowB : Fin n → Equiv.Perm (Fin n) := fun x =>
    Equiv.ofBijective (B x) ⟨hBi x, Finite.surjective_of_injective (hBi x)⟩
  let fa : Fin n → Fin n := fun x => (rowA x).symm a
  let fb : Fin n → Fin n := fun x => (rowB x).symm b
  have ha : ∀ x, A x (fa x) = a := fun x => (rowA x).apply_symm_apply a
  have hb : ∀ x, B x (fb x) = b := fun x => (rowB x).apply_symm_apply b
  have hfa : Function.Involutive fa := by
    intro x; apply hAi (fa x); rw [ha, hAs, ha]
  have hfb : Function.Involutive fb := by
    intro x; apply hBi (fb x); rw [hb, hBs, hb]
  have hafix : ∀ x, fa x = x ↔ x = a := by
    intro x
    constructor
    · intro h; have hh := ha x; rwa [h,hAd] at hh
    · intro h; rw [h]; apply hAi a; rw [ha,hAd]
  have hbfix : ∀ x, fb x = x ↔ x = b := by
    intro x
    constructor
    · intro h; have hh := hb x; rwa [h,hBd] at hh
    · intro h; rw [h]; apply hBi b; rw [hb,hBd]
  let f : Equiv.Perm (Fin n) := ⟨fa,fa,hfa,hfa⟩
  let g : Equiv.Perm (Fin n) := ⟨fb,fb,hfb,hfb⟩
  have hc : (univ.filter fun x => f x = x).card =
      (univ.filter fun x => g x = x).card := by
    change (univ.filter fun x => fa x = x).card =
      (univ.filter fun x => fb x = x).card
    simp only [hafix,hbfix,filter_eq',mem_univ,if_true,card_singleton]
  obtain ⟨e, he⟩ := wild_involutions_conjugate_of_fixed_count f g hfa hfb hc
  have he' : ∀ x, e (fa x) = fb (e x) := he
  have hea : e a = b := by
    apply (hbfix _).mp
    rw [← he', (hafix a).mpr rfl]
  refine ⟨e,hea,?_⟩
  intro x y
  constructor
  · intro h
    have hh : e y = fb (e x) := hBi (e x) (h.trans (hb _).symm)
    have hy : y = fa x := e.injective (hh.trans (he' x).symm)
    rw [hy,ha]
  · intro h
    have hy : y = fa x := hAi x (h.trans (ha x).symm)
    rw [hy,he',hb]
