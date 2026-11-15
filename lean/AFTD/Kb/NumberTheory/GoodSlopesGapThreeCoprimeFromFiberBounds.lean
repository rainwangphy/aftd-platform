import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopes
import AFTD.Kb.NumberTheory.IsExtremalPerm
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesTwoRowFiberRigidityConditional
import AFTD.Kb.NumberTheory.GoodSlopesMemIff

/-!
# good_slopes_gap_three_coprime_from_fiber_bounds

Topic: elementary_number_theory   Node: ca9c49bd0247

Provenance: helper lemma. Conditional general CRT reduction for OP-1027, adapting the proof of good_slopes_gap_mod_105.

Let k be a nonzero natural number coprime to 3 and let f be a non-extremal permutation modulo 3k. Suppose there are L units modulo k and 0 < d with 2d < L, and suppose a shift c takes every good slope of f to a unit modulo 3k. Assume every k-point fiber with a bad unit direction has at most L-d good unit directions, while every such fiber with a three-coloring that makes the first coordinate and every unit-direction form injective within each color has at most L-2d good unit directions. Then f has at most 2L-2d good slopes.
-/

open Finset

private lemma good_slopes_gap_three_coprime_from_fiber_bounds_units_three_mul_k
    (k L : ℕ) [NeZero k] (hcop : Nat.Coprime 3 k)
    (hL : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b).card = L) :
    ((Finset.univ : Finset (ZMod (3 * k))).filter fun b => IsUnit b).card = 2 * L := by
  have e := ZMod.chineseRemainder hcop
  have h_image : ((Finset.univ : Finset (ZMod (3 * k))).filter fun b => IsUnit b).map e.toEquiv.toEmbedding =
      ((univ : Finset (ZMod 3)).filter IsUnit) ×ˢ ((univ : Finset (ZMod k)).filter IsUnit) := by
    ext ⟨a, b⟩
    simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding, mem_product]
    constructor
    · rintro ⟨x, hx, heq⟩
      have hu : IsUnit (e x) := (MulEquiv.isUnit_map e).mpr hx
      have heq' : e x = (a, b) := heq
      rw [heq', Prod.isUnit_iff] at hu
      exact hu
    · rintro ⟨ha, hb⟩
      have hu : IsUnit (a, b) := Prod.isUnit_iff.mpr ⟨ha, hb⟩
      refine ⟨e.symm (a, b), ?_, e.apply_symm_apply (a, b)⟩
      exact (MulEquiv.isUnit_map e).mp (by rwa [e.apply_symm_apply])
  have h_card := congr_arg Finset.card h_image
  rw [card_map, card_product, hL] at h_card
  have h3 : ((univ : Finset (ZMod 3)).filter IsUnit).card = 2 := by decide
  rw [h3] at h_card
  exact h_card

private lemma good_slopes_gap_three_coprime_from_fiber_bounds_filter_isUnit_eq_totient
    (n : ℕ) [NeZero n] :
    ((Finset.univ : Finset (ZMod n)).filter fun b => IsUnit b).card = Nat.totient n := by
  classical
  rw [← ZMod.card_units_eq_totient]
  have e1 := ZMod.unitsEquivCoprime (n := n)
  have e2 : { x : ZMod n // Nat.Coprime x.val n } ≃ { x : ZMod n // IsUnit x } := by
    refine Equiv.subtypeEquivRight (fun x => ?_)
    have := ZMod.isUnit_iff_coprime x.val n
    rw [ZMod.natCast_zmod_val] at this
    exact this.symm
  rw [Fintype.card_congr (e1.trans e2)]
  exact (Fintype.card_subtype (fun b : ZMod n => IsUnit b)).symm

private lemma good_slopes_gap_three_coprime_from_fiber_bounds_totient_three_mul_eq_two_mul
    (k L : ℕ) [NeZero k] (hcop : Nat.Coprime 3 k)
    (hL : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b).card = L) :
    Nat.totient (3 * k) = 2 * L := by
  have : NeZero (3 * k) := inferInstance
  rw [← good_slopes_gap_three_coprime_from_fiber_bounds_filter_isUnit_eq_totient (3 * k)]
  exact good_slopes_gap_three_coprime_from_fiber_bounds_units_three_mul_k k L hcop hL

private lemma good_slopes_gap_three_coprime_from_fiber_bounds_zmod3_isUnit (a : ZMod 3) :
    IsUnit a ↔ a = 1 ∨ a = 2 := by
  revert a; decide

theorem good_slopes_gap_three_coprime_from_fiber_bounds (k L d : ℕ) [NeZero k] (hcop : Nat.Coprime 3 k) (f : Equiv.Perm (ZMod (3*k))) (hf : ¬ is_extremal_perm (3*k) f) (hcover : ∃ c : ZMod (3*k), ∀ m ∈ good_slopes (3*k) f, IsUnit (m+c)) (hL : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b).card = L) (hd : 0 < d) (hLd : 2*d < L) (hgap : ∀ S : Finset (ZMod k × ZMod k), S.card = k → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-d) (hcolored : ∀ (S : Finset (ZMod k × ZMod k)) (color : (ZMod k × ZMod k) → Fin 3), S.card = k → (∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q) → (∀ b : ZMod k, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-2*d) : (good_slopes (3*k) f).card ≤ 2*L-2*d := by
  classical
  by_contra hnot
  have hlarge : 2*L-2*d < (good_slopes (3*k) f).card := by omega
  obtain ⟨c, hcover⟩ := hcover
  let e := ZMod.chineseRemainder hcop
  let normalized : ZMod (3*k) → ZMod (3*k) := fun x => f x - c*x
  let A : Finset (ZMod (3*k)) := (good_slopes (3*k) f).image (fun m => m+c)
  have hA (u : ZMod (3*k)) : u ∈ A ↔ Function.Injective (fun x => normalized x + u*x) := by
    rw [Finite.injective_iff_bijective]
    constructor
    · intro hu
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hu
      rw [good_slopes_mem_iff] at hm
      have he : (fun x => normalized x + (m+c)*x) = (fun x => f x + m*x) := by
        funext x; dsimp [normalized]; ring
      rw [he]
      exact hm
    · intro hu
      apply mem_image.mpr
      refine ⟨u - c, ?_, by ring⟩
      rw [good_slopes_mem_iff]
      have he : (fun x => f x + (u-c)*x) = (fun x => normalized x + u*x) := by
        funext x; dsimp [normalized]; ring
      rw [he]
      exact hu
  have hAunit : ∀ u ∈ A, IsUnit u := by
    intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hu
    exact hcover m hm
  have hAcard : A.card = (good_slopes (3*k) f).card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  let pairs : Finset (ZMod 3 × ZMod k) := A.image e
  have hFcard : pairs.card = A.card := Finset.card_image_of_injective _ e.injective
  have hFmem (a : ZMod 3) (b : ZMod k) : (a, b) ∈ pairs ↔ e.symm (a, b) ∈ A := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := mem_image.mp h
      have heq : u = e.symm (a, b) := by
        apply_fun e.symm at he
        rwa [e.symm_apply_apply] at he
      rwa [← heq]
    · intro h
      exact mem_image.mpr ⟨e.symm (a, b), h, e.apply_symm_apply (a, b)⟩
  have hF (a : ZMod 3) (b : ZMod k) : (a, b) ∈ pairs ↔
      IsUnit a ∧ IsUnit b ∧ Function.Injective (fun x : ZMod (3*k) =>
        ((e (normalized x)).1 + a * (e x).1, (e (normalized x)).2 + b * (e x).2)) := by
    constructor
    · intro h
      have hu : IsUnit (e.symm (a, b)) := hAunit _ ((hFmem a b).1 h)
      have huv : IsUnit a ∧ IsUnit b := by
        have hu' : IsUnit (e (e.symm (a, b))) := (MulEquiv.isUnit_map e).2 hu
        rw [e.apply_symm_apply] at hu'
        exact Prod.isUnit_iff.1 hu'
      have hinj : Function.Injective (fun x => normalized x + e.symm (a, b) * x) :=
        (hA _).1 ((hFmem a b).1 h)
      refine ⟨huv.1, huv.2, ?_⟩
      have heq : (fun x => ((e (normalized x)).1 + a * (e x).1, (e (normalized x)).2 + b * (e x).2)) =
          e ∘ (fun x => normalized x + e.symm (a, b) * x) := by
        funext x
        dsimp
        rw [RingEquiv.map_add, RingEquiv.map_mul, e.apply_symm_apply]
        rfl
      rw [heq]
      exact e.injective.comp hinj
    · rintro ⟨ha, hb, hi⟩
      apply (hFmem a b).2
      apply (hA _).2
      have heq : (fun x => ((e (normalized x)).1 + a * (e x).1, (e (normalized x)).2 + b * (e x).2)) =
          e ∘ (fun x => normalized x + e.symm (a, b) * x) := by
        funext x
        dsimp
        rw [RingEquiv.map_add, RingEquiv.map_mul, e.apply_symm_apply]
        rfl
      rw [heq] at hi
      intro x y hxy
      exact hi (congr_arg e hxy)
  let R : ZMod 3 → Finset (ZMod k) := fun a => univ.filter fun b =>
    IsUnit b ∧ Function.Injective (fun x : ZMod (3*k) =>
      ((e (normalized x)).1 + a * (e x).1, (e (normalized x)).2 + b * (e x).2))
  have hdecomp : pairs = (({1} : Finset (ZMod 3)) ×ˢ R 1) ∪ (({2} : Finset (ZMod 3)) ×ˢ R 2) := by
    ext ⟨a, b⟩
    rw [hF a b]
    simp only [mem_union, mem_product, mem_singleton, R, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨ha, hb, hi⟩
      rcases (good_slopes_gap_three_coprime_from_fiber_bounds_zmod3_isUnit a).1 ha with rfl | rfl
      · left; exact ⟨rfl, hb, hi⟩
      · right; exact ⟨rfl, hb, hi⟩
    · rintro (⟨rfl, hb, hi⟩ | ⟨rfl, hb, hi⟩)
      · exact ⟨(good_slopes_gap_three_coprime_from_fiber_bounds_zmod3_isUnit 1).2 (Or.inl rfl), hb, hi⟩
      · exact ⟨(good_slopes_gap_three_coprime_from_fiber_bounds_zmod3_isUnit 2).2 (Or.inr rfl), hb, hi⟩
  have hdisj : Disjoint (({1} : Finset (ZMod 3)) ×ˢ R 1) (({2} : Finset (ZMod 3)) ×ˢ R 2) := by
    apply Finset.disjoint_left.mpr
    intro ⟨a, b⟩ h1 h2
    simp only [mem_product, mem_singleton] at h1 h2
    have h12 : (1 : ZMod 3) ≠ 2 := by decide
    exact h12 (h1.1.symm.trans h2.1)
  have hcount : pairs.card = (R 1).card + (R 2).card := by
    rw [hdecomp, card_union_of_disjoint hdisj, card_product, card_product]
    simp
  have hrows : 2*L-2*d < (R 1).card + (R 2).card := by
    rw [← hcount, hFcard, hAcard]
    exact hlarge
  have : Nonempty (ZMod (3 * k)) := inferInstance
  have hcard : Fintype.card (ZMod (3 * k)) = 3 * k := ZMod.card (3 * k)
  have hx : Function.Injective (fun x : ZMod (3 * k) => ((e x).1, (e x).2)) := by
    intro x y hxy
    exact e.injective (Prod.ext (congr_arg Prod.fst hxy) (congr_arg Prod.snd hxy))
  have hstrong := good_slopes_two_row_fiber_rigidity_conditional k L d
    (fun x => (e x).1) (fun x => (e (normalized x)).1)
    (fun x => (e x).2) (fun x => (e (normalized x)).2)
    1 2
    hcard hx hL hd hLd hgap hcolored
    (by simpa [R] using hrows)
  have hAll : ∀ u : ZMod (3*k), IsUnit u → u ∈ A := by
    intro u hu
    have hu' : IsUnit (e u) := (MulEquiv.isUnit_map e).2 hu
    rw [Prod.isUnit_iff] at hu'
    have ha := (good_slopes_gap_three_coprime_from_fiber_bounds_zmod3_isUnit _).1 hu'.1
    apply (hA u).2
    rcases ha with ha | ha
    · have h1 := hstrong.1 (e u).2 hu'.2
      have heq : (fun x => ((e (normalized x)).1 + (e u).1 * (e x).1, (e (normalized x)).2 + (e u).2 * (e x).2)) =
          e ∘ (fun x => normalized x + u * x) := by
        funext x
        dsimp
        rw [RingEquiv.map_add, RingEquiv.map_mul]
        rfl
      rw [ha] at heq
      rw [heq] at h1
      intro x y hxy
      exact h1 (congr_arg e hxy)
    · have h2 := hstrong.2 (e u).2 hu'.2
      have heq : (fun x => ((e (normalized x)).1 + (e u).1 * (e x).1, (e (normalized x)).2 + (e u).2 * (e x).2)) =
          e ∘ (fun x => normalized x + u * x) := by
        funext x
        dsimp
        rw [RingEquiv.map_add, RingEquiv.map_mul]
        rfl
      rw [ha] at heq
      rw [heq] at h2
      intro x y hxy
      exact h2 (congr_arg e hxy)
  let U : Finset (ZMod (3*k)) := univ.filter fun u => IsUnit u
  have hAU : A = U := by
    ext u
    simp only [U, mem_filter, mem_univ, true_and]
    exact ⟨hAunit u, hAll u⟩
  have hUcard : U.card = 2 * L := good_slopes_gap_three_coprime_from_fiber_bounds_units_three_mul_k k L hcop hL
  apply hf
  unfold is_extremal_perm
  have ht : Nat.totient (3*k) = 2 * L := good_slopes_gap_three_coprime_from_fiber_bounds_totient_three_mul_eq_two_mul k L hcop hL
  rw [hAU, hUcard] at hAcard
  exact hAcard.symm.trans ht.symm
