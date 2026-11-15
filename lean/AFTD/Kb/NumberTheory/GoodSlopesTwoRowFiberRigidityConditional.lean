import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberTransfer
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberSet

/-!
# good_slopes_two_row_fiber_rigidity_conditional

Topic: elementary_number_theory   Node: cf438d2c8631

Provenance: helper lemma. Conditional CRT fiber reduction for OP-1027, generalizing the proved modulus-35 two-row reduction.

Let k be nonzero and let X be a finite set of size 3k whose input coordinates in Z/3 and Z/k form an injective pair. Suppose there are L units modulo k and 0 < d with 2d < L. Assume every k-point fiber with a bad unit direction has at most L-d good unit directions, and every such fiber whose points have a three-coloring that makes the first coordinate and every unit-direction form injective within each color has at most L-2d good unit directions. For any two fixed first-coordinate slopes, if the numbers of unit second-coordinate slopes giving injective coordinate maps sum to more than 2L-2d, then all unit second-coordinate slopes give injective maps in both rows.
-/

open Finset

lemma good_slopes_two_row_fiber_rigidity_conditional_uncolored_transfer
    (k L d : ℕ) [NeZero k] {X : Type*} [Fintype X] [DecidableEq X]
    (x3 y3 : X → ZMod 3) (xk yk : X → ZMod k) (q : ZMod 3) (b₀ : ZMod k)
    (hcard : Fintype.card X = 3 * k)
    (hgap : ∀ S : Finset (ZMod k × ZMod k), S.card = k →
      (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) →
      (good_slopes_point_directions k S).card ≤ L - d)
    (hanchor : Function.Bijective (fun x => (y3 x + q*x3 x, yk x + b₀*xk x)))
    (hbad : ∃ b : ZMod k, IsUnit b ∧ ¬ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))) :
    ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))).card ≤ L - d := by
  have hcard' : Fintype.card X = Fintype.card (ZMod 3) * Fintype.card (ZMod k) := by
    simp [hcard]
  have htransfer := good_slopes_product_fiber_transfer x3 y3 xk yk q b₀ hcard' hanchor
  rcases hbad with ⟨b, hb, hbinj⟩
  have ht_bad : ∃ t : ZMod 3, b ∉ good_slopes_point_directions k (good_slopes_product_fiber_set x3 y3 xk yk q t) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hall : ∀ t : ZMod 3, Set.InjOn (fun p : ZMod k × ZMod k => p.2 + b * p.1) (good_slopes_product_fiber_set x3 y3 xk yk q t) := by
      intro t
      have ht := h t
      unfold good_slopes_point_directions at ht
      simp only [mem_filter, mem_univ, true_and] at ht
      exact ht.2
    exact hbinj (htransfer.2.2 b hall)
  obtain ⟨t, ht⟩ := ht_bad
  set S := good_slopes_product_fiber_set x3 y3 xk yk q t
  have hScard : S.card = k := by
    have h1 := htransfer.1 t
    rw [ZMod.card] at h1
    exact h1
  have hgap_S : (good_slopes_point_directions k S).card ≤ L - d :=
    hgap S hScard ⟨b, hb, ht⟩
  have hsub : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))) ⊆ good_slopes_point_directions k S := by
    intro b' hb'
    simp only [mem_filter, mem_univ, true_and] at hb'
    unfold good_slopes_point_directions
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨hb'.1, htransfer.2.1 t b' hb'.2⟩
  exact (Finset.card_le_card hsub).trans hgap_S

lemma good_slopes_two_row_fiber_rigidity_conditional_colored_transfer
    (k L d : ℕ) [NeZero k] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (x3 y3 : X → ZMod 3) (xk yk : X → ZMod k) (q q' : ZMod 3) (b₀ : ZMod k)
    (hcard : Fintype.card X = 3 * k)
    (hx : Function.Injective (fun x => (x3 x, xk x)))
    (hcolored : ∀ (S : Finset (ZMod k × ZMod k)) (c : (ZMod k × ZMod k) → Fin 3),
      S.card = k →
      (∀ p ∈ S, ∀ q ∈ S, c p = c q → p.1 = q.1 → p = q) →
      (∀ b : ZMod k, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) →
      (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) →
      (good_slopes_point_directions k S).card ≤ L - 2*d)
    (hanchor : Function.Bijective (fun x => (y3 x + q*x3 x, yk x + b₀*xk x)))
    (hcomplete : ∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (y3 x + q'*x3 x, yk x + b*xk x)))
    (hbad : ∃ b : ZMod k, IsUnit b ∧ ¬ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))) :
    ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))).card ≤ L - 2*d := by
  have hcard' : Fintype.card X = Fintype.card (ZMod 3) * Fintype.card (ZMod k) := by
    simp [hcard]
  have htransfer := good_slopes_product_fiber_transfer x3 y3 xk yk q b₀ hcard' hanchor
  rcases hbad with ⟨b, hb, hbinj⟩
  have ht_bad : ∃ t : ZMod 3, b ∉ good_slopes_point_directions k (good_slopes_product_fiber_set x3 y3 xk yk q t) := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hall : ∀ t : ZMod 3, Set.InjOn (fun p : ZMod k × ZMod k => p.2 + b * p.1) (good_slopes_product_fiber_set x3 y3 xk yk q t) := by
      intro t
      have ht := h t
      unfold good_slopes_point_directions at ht
      simp only [mem_filter, mem_univ, true_and] at ht
      exact ht.2
    exact hbinj (htransfer.2.2 b hall)
  obtain ⟨t, ht⟩ := ht_bad
  set S := good_slopes_product_fiber_set x3 y3 xk yk q t
  have hScard : S.card = k := by
    have h1 := htransfer.1 t
    rw [ZMod.card] at h1
    exact h1
  have h_rep : ∀ p : ZMod k × ZMod k, ∃ x : X, p ∈ S → y3 x + q * x3 x = t ∧ (xk x, yk x) = p := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ univ.filter (fun x => y3 x + q * x3 x = t), (xk x, yk x) = p := by
        exact Finset.mem_image.mp hp
      rw [Finset.mem_filter] at hx
      exact ⟨x, fun _ => ⟨hx.2, rfl⟩⟩
    · obtain ⟨x0⟩ := ‹Nonempty X›
      exact ⟨x0, fun hp' => (hp hp').elim⟩
  choose rep hrep using h_rep
  let c : (ZMod k × ZMod k) → Fin 3 := fun p => ⟨(x3 (rep p)).val, ZMod.val_lt _⟩
  have hcolor1 : ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.1 = q.1 → p = q := by
    intro p hp q_pt hq_pt hc hp1
    obtain ⟨_, hp_eq⟩ := hrep p hp
    obtain ⟨_, hq_eq⟩ := hrep q_pt hq_pt
    have hc_val : (x3 (rep p)).val = (x3 (rep q_pt)).val := by
      injection hc
    have hc_eq : x3 (rep p) = x3 (rep q_pt) := ZMod.val_injective 3 hc_val
    have hxk_eq : xk (rep p) = xk (rep q_pt) := by
      rw [← hp_eq, ← hq_eq] at hp1
      exact hp1
    have hrep_eq : rep p = rep q_pt := by
      apply hx
      exact Prod.ext hc_eq hxk_eq
    rw [← hp_eq, ← hq_eq, hrep_eq]
  have hcolor2 : ∀ b' : ZMod k, IsUnit b' → ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.2 + b'*p.1 = q.2 + b'*q.1 → p = q := by
    intro b' hb' p hp q_pt hq_pt hc hform
    obtain ⟨ht_p, hp_eq⟩ := hrep p hp
    obtain ⟨ht_q, hq_eq⟩ := hrep q_pt hq_pt
    have hc_val : (x3 (rep p)).val = (x3 (rep q_pt)).val := by
      injection hc
    have hc_eq : x3 (rep p) = x3 (rep q_pt) := ZMod.val_injective 3 hc_val
    have hy3_eq : y3 (rep p) = y3 (rep q_pt) := by
      calc y3 (rep p) = (y3 (rep p) + q * x3 (rep p)) - q * x3 (rep p) := by ring
      _ = t - q * x3 (rep p) := by rw [ht_p]
      _ = t - q * x3 (rep q_pt) := by rw [hc_eq]
      _ = (y3 (rep q_pt) + q * x3 (rep q_pt)) - q * x3 (rep q_pt) := by rw [ht_q]
      _ = y3 (rep q_pt) := by ring
    have hrow3 : y3 (rep p) + q' * x3 (rep p) = y3 (rep q_pt) + q' * x3 (rep q_pt) := by
      rw [hy3_eq, hc_eq]
    have hp1 : p.1 = xk (rep p) := congr_arg Prod.fst hp_eq.symm
    have hp2 : p.2 = yk (rep p) := congr_arg Prod.snd hp_eq.symm
    have hq1 : q_pt.1 = xk (rep q_pt) := congr_arg Prod.fst hq_eq.symm
    have hq2 : q_pt.2 = yk (rep q_pt) := congr_arg Prod.snd hq_eq.symm
    have hrowk : yk (rep p) + b' * xk (rep p) = yk (rep q_pt) + b' * xk (rep q_pt) := by
      linear_combination hform - hp2 - b' * hp1 + hq2 + b' * hq1
    have hpair : (y3 (rep p) + q' * x3 (rep p), yk (rep p) + b' * xk (rep p)) =
                 (y3 (rep q_pt) + q' * x3 (rep q_pt), yk (rep q_pt) + b' * xk (rep q_pt)) :=
      Prod.ext hrow3 hrowk
    have hrep_eq : rep p = rep q_pt := hcomplete b' hb' hpair
    rw [← hp_eq, ← hq_eq, hrep_eq]
  have hcolored_S : (good_slopes_point_directions k S).card ≤ L - 2*d :=
    hcolored S c hScard hcolor1 hcolor2 ⟨b, hb, ht⟩
  have hsub : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))) ⊆ good_slopes_point_directions k S := by
    intro b' hb'
    simp only [mem_filter, mem_univ, true_and] at hb'
    unfold good_slopes_point_directions
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨hb'.1, htransfer.2.1 t b' hb'.2⟩
  exact (Finset.card_le_card hsub).trans hcolored_S

theorem good_slopes_two_row_fiber_rigidity_conditional (k L d : ℕ) [NeZero k] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (x3 y3 : X → ZMod 3) (xk yk : X → ZMod k) (a a' : ZMod 3) (hcard : Fintype.card X = 3*k) (hx : Function.Injective (fun x => (x3 x, xk x))) (hL : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b).card = L) (hd : 0 < d) (hLd : 2*d < L) (hgap : ∀ S : Finset (ZMod k × ZMod k), S.card = k → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-d) (hcolored : ∀ (S : Finset (ZMod k × ZMod k)) (c : (ZMod k × ZMod k) → Fin 3), S.card = k → (∀ p ∈ S, ∀ q ∈ S, c p = c q → p.1 = q.1 → p = q) → (∀ b : ZMod k, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, c p = c q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-2*d) (hlarge : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + a*x3 x, yk x + b*xk x))).card + ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + a'*x3 x, yk x + b*xk x))).card > 2*L-2*d) : (∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (y3 x + a*x3 x, yk x + b*xk x))) ∧ (∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (y3 x + a'*x3 x, yk x + b*xk x))) := by
  classical
  let R : ZMod 3 → Finset (ZMod k) := fun q => univ.filter fun b => IsUnit b ∧ Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x))
  have hlarge' : 2*L - 2*d < (R a).card + (R a').card := hlarge
  have hbound (q : ZMod 3) : (R q).card ≤ L := by
    have hsub : R q ⊆ univ.filter (fun b : ZMod k => IsUnit b) := by
      intro b hb
      simp only [R, mem_filter, mem_univ, true_and] at hb ⊢
      exact hb.1
    have h := Finset.card_le_card hsub
    omega
  have ha : 0 < (R a).card := by have := hbound a'; omega
  have ha' : 0 < (R a').card := by have := hbound a; omega
  have anchor (q : ZMod 3) (h : 0 < (R q).card) : ∃ b : ZMod k,
      Function.Bijective (fun x => (y3 x + q*x3 x, yk x + b*xk x)) := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp h
    simp only [R, mem_filter, mem_univ, true_and] at hb
    refine ⟨b, (Fintype.bijective_iff_injective_and_card _).2 ⟨hb.2, ?_⟩⟩
    rw [Fintype.card_prod, ZMod.card, ZMod.card, hcard]
  obtain ⟨b0, hb0⟩ := anchor a ha
  obtain ⟨b1, hb1⟩ := anchor a' ha'
  have key (q q' : ZMod 3) (c0 c1 : ZMod k)
      (hc0 : Function.Bijective (fun x => (y3 x + q*x3 x, yk x + c0*xk x)))
      (hc1 : Function.Bijective (fun x => (y3 x + q'*x3 x, yk x + c1*xk x)))
      (hl : 2*L - 2*d < (R q).card + (R q').card) :
      ∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (y3 x + q*x3 x, yk x + b*xk x)) := by
    intro b hb
    by_contra hbad
    have hLd_q : (R q).card ≤ L - d :=
      good_slopes_two_row_fiber_rigidity_conditional_uncolored_transfer k L d x3 y3 xk yk q c0 hcard hgap hc0 ⟨b, hb, hbad⟩
    have hfull : ∀ d' : ZMod k, IsUnit d' → Function.Injective (fun x => (y3 x + q'*x3 x, yk x + d'*xk x)) := by
      intro d' hd'
      by_contra hbad'
      have hLd_q' : (R q').card ≤ L - d :=
        good_slopes_two_row_fiber_rigidity_conditional_uncolored_transfer k L d x3 y3 xk yk q' c1 hcard hgap hc1 ⟨d', hd', hbad'⟩
      omega
    have hL2d : (R q).card ≤ L - 2*d :=
      good_slopes_two_row_fiber_rigidity_conditional_colored_transfer k L d x3 y3 xk yk q q' c0 hcard hx hcolored hc0 hfull ⟨b, hb, hbad⟩
    have := hbound q'
    omega
  exact ⟨key a a' b0 b1 hb0 hb1 hlarge', key a' a b1 b0 hb1 hb0 (by omega)⟩
