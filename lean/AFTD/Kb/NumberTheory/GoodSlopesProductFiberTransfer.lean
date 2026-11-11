import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberSet
import AFTD.Kb.NumberTheory.GoodSlopesInjectiveProductFiberCard

/-!
# good_slopes_product_fiber_transfer

Topic: elementary_number_theory   Node: ed89fa43d6d5

Provenance: helper lemma. CRT projection step in the 105-point reduction of OP-1027.

For a bijective anchor direction on a product, each projected fiber has the size of the second factor. Good directions with the same first coordinate remain good in every fiber, and conversely injectivity in every fiber implies global injectivity.
-/

theorem good_slopes_product_fiber_transfer {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [CommRing Y] [DecidableEq Y] [Fintype Z] [CommRing Z] [DecidableEq Z] (xY yY : X → Y) (xZ yZ : X → Z) (a : Y) (b₀ : Z) (hcard : Fintype.card X = Fintype.card Y * Fintype.card Z) (hanchor : Function.Bijective (fun x => (yY x + a*xY x, yZ x + b₀*xZ x))) : (∀ t : Y, (good_slopes_product_fiber_set xY yY xZ yZ a t).card = Fintype.card Z) ∧ (∀ (t : Y) (b : Z), Function.Injective (fun x => (yY x + a*xY x, yZ x + b*xZ x)) → Set.InjOn (fun p : Z × Z => p.2 + b*p.1) (good_slopes_product_fiber_set xY yY xZ yZ a t)) ∧ (∀ b : Z, (∀ t : Y, Set.InjOn (fun p : Z × Z => p.2 + b*p.1) (good_slopes_product_fiber_set xY yY xZ yZ a t)) → Function.Injective (fun x => (yY x + a*xY x, yZ x + b*xZ x))) := by
  classical
  let F : Y → Finset X := fun t => Finset.univ.filter fun x => yY x + a*xY x = t
  let Q : X → Z × Z := fun x => (xZ x,yZ x)
  have hproj (t : Y) : Set.InjOn Q (F t) := by
    intro x hx y hy heq
    apply hanchor.1
    apply Prod.ext
    · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    · have hxz := congrArg Prod.fst heq
      have hyz := congrArg Prod.snd heq
      dsimp [Q] at hxz hyz
      change yZ x + b₀*xZ x = yZ y + b₀*xZ y
      rw [hxz,hyz]
  have hfcard (t : Y) : (F t).card = Fintype.card Z := by
    have hh := good_slopes_injective_product_fiber_card Finset.univ
      (fun x : X => (yY x + a*xY x, yZ x + b₀*xZ x))
      (by intro x _ y _ h; exact hanchor.1 h) (by simpa using hcard) t
    simpa [F] using hh
  have hP (t : Y) : good_slopes_product_fiber_set xY yY xZ yZ a t = (F t).image Q := by
    rfl
  refine ⟨?_,?_,?_⟩
  · intro t
    rw [hP,Finset.card_image_of_injOn (hproj t),hfcard]
  · intro t b hgood p hp q hq heq
    rw [hP] at hp hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    have hxy : x = y := by
      apply hgood
      apply Prod.ext
      · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      · exact heq
    exact congrArg Q hxy
  · intro b hlocal x y heq
    let t := yY x + a*xY x
    have hx : x ∈ F t := by simp [F,t]
    have hy : y ∈ F t := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      exact (congrArg Prod.fst heq).symm
    have hqx : Q x ∈ good_slopes_product_fiber_set xY yY xZ yZ a t := by
      rw [hP]
      exact Finset.mem_image_of_mem _ hx
    have hqy : Q y ∈ good_slopes_product_fiber_set xY yY xZ yZ a t := by
      rw [hP]
      exact Finset.mem_image_of_mem _ hy
    have hq : Q x = Q y := hlocal t hqx hqy (congrArg Prod.snd heq)
    exact hproj t hx hy hq
