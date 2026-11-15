import AFTD.Prelude
import AFTD.Kb.NumberTheory.GoodSlopesPointDirections
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberTransfer
import AFTD.Kb.NumberTheory.GoodSlopesProductFiberSet

/-!
# good_slopes_many_row_fiber_rigidity_conditional

Topic: elementary_number_theory   Node: e62e94c1a70a

Provenance: helper lemma. Conditional many-row product-fiber reduction for OP-1027, generalizing good_slopes_two_row_fiber_rigidity_conditional.

Let K be a finite field with r nonzero elements and let k be nonzero. Let X have |K|·k elements and input coordinates in K×Z/kZ that form an injective pair. Suppose there are L units modulo k, d is positive and r·d<L. Assume that every k-point set with a bad unit direction has at most L−d good unit directions, and that a set with a bad direction and a K-coloring that makes the input coordinate and all unit direction forms injective within colors has at most L−r·d good unit directions. If the total number of good unit directions across all nonzero K-coordinate rows is greater than rL−rd, then every row is full.
-/

theorem good_slopes_many_row_fiber_rigidity_conditional_uncolored
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] (k L d : ℕ) [NeZero k]
    {X : Type*} [Fintype X] [DecidableEq X]
    (xK yK : X → K) (xk yk : X → ZMod k) (a : K) (b₀ : ZMod k)
    (hcard : Fintype.card X = Fintype.card K * k)
    (hgap : ∀ S : Finset (ZMod k × ZMod k), S.card = k →
      (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) →
      (good_slopes_point_directions k S).card ≤ L-d)
    (hanchor : Function.Bijective (fun x => (yK x + a*xK x, yk x + b₀*xk x)))
    (hbad : ∃ b : ZMod k, IsUnit b ∧ ¬ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x))) :
    ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x))).card ≤ L - d := by
  classical
  have hcard' : Fintype.card X = Fintype.card K * Fintype.card (ZMod k) := by
    rw [ZMod.card]; exact hcard
  have htransfer := good_slopes_product_fiber_transfer xK yK xk yk a b₀ hcard' hanchor
  obtain ⟨b, hbunit, hbinj⟩ := hbad
  have hnotall : ¬ ∀ t : K, Set.InjOn (fun p : ZMod k × ZMod k => p.2 + b*p.1) ↑(good_slopes_product_fiber_set xK yK xk yk a t) := by
    intro hall
    exact hbinj (htransfer.2.2 b hall)
  push_neg at hnotall
  obtain ⟨t, ht⟩ := hnotall
  have hScard : (good_slopes_product_fiber_set xK yK xk yk a t).card = k := by
    have := htransfer.1 t
    rwa [ZMod.card] at this
  have hSbad : ∃ b' : ZMod k, IsUnit b' ∧ b' ∉ good_slopes_point_directions k (good_slopes_product_fiber_set xK yK xk yk a t) := by
    refine ⟨b, hbunit, fun hmem => ?_⟩
    simp only [good_slopes_point_directions, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ht hmem.2
  have hgapS := hgap _ hScard hSbad
  refine le_trans ?_ hgapS
  apply Finset.card_le_card
  intro b' hb'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, good_slopes_point_directions] at hb' ⊢
  exact ⟨hb'.1, htransfer.2.1 t b' hb'.2⟩

theorem good_slopes_many_row_fiber_rigidity_conditional_colored
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] (k L r d : ℕ) [NeZero k]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (xK yK : X → K) (xk yk : X → ZMod k) (a a1 : K) (b₀ : ZMod k)
    (hcard : Fintype.card X = Fintype.card K * k)
    (hx : Function.Injective (fun x => (xK x, xk x)))
    (hcolored : ∀ (S : Finset (ZMod k × ZMod k)) (color : (ZMod k × ZMod k) → K), S.card = k →
      (∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q) →
      (∀ b : ZMod k, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) →
      (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) →
      (good_slopes_point_directions k S).card ≤ L-r*d)
    (hanchor : Function.Bijective (fun x => (yK x + a*xK x, yk x + b₀*xk x)))
    (hfull : ∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (yK x + a1*xK x, yk x + b*xk x)))
    (hbad : ∃ b : ZMod k, IsUnit b ∧ ¬ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x))) :
    ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x))).card ≤ L - r*d := by
  classical
  have hcard' : Fintype.card X = Fintype.card K * Fintype.card (ZMod k) := by
    rw [ZMod.card]; exact hcard
  have htransfer := good_slopes_product_fiber_transfer xK yK xk yk a b₀ hcard' hanchor
  obtain ⟨b, hbunit, hbinj⟩ := hbad
  have hnotall : ¬ ∀ t : K, Set.InjOn (fun p : ZMod k × ZMod k => p.2 + b*p.1) ↑(good_slopes_product_fiber_set xK yK xk yk a t) := by
    intro hall
    exact hbinj (htransfer.2.2 b hall)
  push_neg at hnotall
  obtain ⟨t, ht⟩ := hnotall
  have hmem_img : ∀ p : ZMod k × ZMod k, p ∈ good_slopes_product_fiber_set xK yK xk yk a t ↔ ∃ x : X, yK x + a*xK x = t ∧ (xk x, yk x) = p := by
    intro p
    simp only [good_slopes_product_fiber_set, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  let rep : (ZMod k × ZMod k) → X := fun p =>
    if hp : ∃ x : X, yK x + a*xK x = t ∧ (xk x, yk x) = p then hp.choose else Classical.arbitrary X
  have hrep_spec : ∀ p, (∃ x : X, yK x + a*xK x = t ∧ (xk x, yk x) = p) → yK (rep p) + a*xK (rep p) = t ∧ (xk (rep p), yk (rep p)) = p := by
    intro p hp
    simp only [rep, dif_pos hp]
    exact hp.choose_spec
  let c : (ZMod k × ZMod k) → K := fun p => xK (rep p)
  have hScard : (good_slopes_product_fiber_set xK yK xk yk a t).card = k := by
    have := htransfer.1 t
    rwa [ZMod.card] at this
  have hcolor1 : ∀ p ∈ good_slopes_product_fiber_set xK yK xk yk a t, ∀ q ∈ good_slopes_product_fiber_set xK yK xk yk a t, c p = c q → p.1 = q.1 → p = q := by
    intro p hp q hq hc h1
    have hp' := (hmem_img p).mp hp
    have hq' := (hmem_img q).mp hq
    obtain ⟨hpf, hpe⟩ := hrep_spec p hp'
    obtain ⟨hqf, hqe⟩ := hrep_spec q hq'
    have hxKeq : xK (rep p) = xK (rep q) := hc
    have hxkeq : xk (rep p) = xk (rep q) := by
      rw [← hpe, ← hqe] at h1
      exact h1
    have : rep p = rep q := hx (Prod.ext hxKeq hxkeq)
    rw [← hpe, ← hqe, this]
  have hcolor2 : ∀ b' : ZMod k, IsUnit b' → ∀ p ∈ good_slopes_product_fiber_set xK yK xk yk a t, ∀ q ∈ good_slopes_product_fiber_set xK yK xk yk a t, c p = c q → p.2 + b'*p.1 = q.2 + b'*q.1 → p = q := by
    intro b' hb' p hp q hq hc hform
    have hp' := (hmem_img p).mp hp
    have hq' := (hmem_img q).mp hq
    obtain ⟨hpf, hpe⟩ := hrep_spec p hp'
    obtain ⟨hqf, hqe⟩ := hrep_spec q hq'
    have hxKeq : xK (rep p) = xK (rep q) := hc
    have hyKeq : yK (rep p) = yK (rep q) := by
      have h1 : yK (rep p) + a*xK (rep p) = yK (rep q) + a*xK (rep q) := by rw [hpf, hqf]
      rw [hxKeq] at h1
      exact add_right_cancel h1
    have hform' : yk (rep p) + b'*xk (rep p) = yk (rep q) + b'*xk (rep q) := by
      rw [← hpe, ← hqe] at hform
      exact hform
    have hfirst : yK (rep p) + a1*xK (rep p) = yK (rep q) + a1*xK (rep q) := by rw [hyKeq, hxKeq]
    have := hfull b' hb' (Prod.ext hfirst hform')
    rw [← hpe, ← hqe, this]
  have hSbad : ∃ b' : ZMod k, IsUnit b' ∧ b' ∉ good_slopes_point_directions k (good_slopes_product_fiber_set xK yK xk yk a t) := by
    refine ⟨b, hbunit, fun hmem => ?_⟩
    simp only [good_slopes_point_directions, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact ht hmem.2
  have hgapS := hcolored _ c hScard hcolor1 hcolor2 hSbad
  refine le_trans ?_ hgapS
  apply Finset.card_le_card
  intro b' hb'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, good_slopes_point_directions] at hb' ⊢
  exact ⟨hb'.1, htransfer.2.1 t b' hb'.2⟩

theorem good_slopes_many_row_fiber_rigidity_conditional (K : Type*) [Field K] [Fintype K] [DecidableEq K] (k L r d : ℕ) [NeZero k] {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (xK yK : X → K) (xk yk : X → ZMod k) (hcard : Fintype.card X = Fintype.card K * k) (hx : Function.Injective (fun x => (xK x, xk x))) (hL : ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b).card = L) (hR : ((Finset.univ : Finset K).filter fun a => IsUnit a).card = r) (hr : 0 < r) (hd : 0 < d) (hLd : r*d < L) (hgap : ∀ S : Finset (ZMod k × ZMod k), S.card = k → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-d) (hcolored : ∀ (S : Finset (ZMod k × ZMod k)) (color : (ZMod k × ZMod k) → K), S.card = k → (∀ p ∈ S, ∀ q ∈ S, color p = color q → p.1 = q.1 → p = q) → (∀ b : ZMod k, IsUnit b → ∀ p ∈ S, ∀ q ∈ S, color p = color q → p.2 + b*p.1 = q.2 + b*q.1 → p = q) → (∃ b : ZMod k, IsUnit b ∧ b ∉ good_slopes_point_directions k S) → (good_slopes_point_directions k S).card ≤ L-r*d) (hlarge : ((Finset.univ : Finset K).filter fun a => IsUnit a).sum (fun a => ((Finset.univ : Finset (ZMod k)).filter fun b => IsUnit b ∧ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x))).card) > r*L-r*d) : ∀ a : K, IsUnit a → ∀ b : ZMod k, IsUnit b → Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x)) := by
  classical
  let D : Finset K := (Finset.univ : Finset K).filter (fun a => IsUnit a)
  let R : K → Finset (ZMod k) := fun a => (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b ∧ Function.Injective (fun x => (yK x + a*xK x, yk x + b*xk x)))
  have hDcard : D.card = r := hR
  have hlarge' : r*L - r*d < D.sum (fun a => (R a).card) := hlarge
  have hbound : ∀ a, (R a).card ≤ L := by
    intro a
    have hsub : R a ⊆ (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b) := by
      intro c hc
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.1
    have := Finset.card_le_card hsub
    rw [hL] at this
    exact this
  intro a ha b hb
  by_contra hcon
  have haD : a ∈ D := by simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]; exact ha
  have hRsubD : R a ⊆ (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b) := by
    intro c hc
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.1
  have hfull_exists : ∃ a1 ∈ D, (R a1).card = L := by
    by_contra hcon2
    have hle : ∀ a' ∈ D, (R a').card ≤ L - d := by
      intro a' ha'
      have hne : (R a').card ≠ L := fun heq => hcon2 ⟨a', ha', heq⟩
      have hbad' : ∃ c : ZMod k, IsUnit c ∧ ¬ Function.Injective (fun x => (yK x + a'*xK x, yk x + c*xk x)) := by
        have hsub : R a' ⊆ (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b) := by
          intro c hc
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
          exact hc.1
        have hcardlt : (R a').card < ((Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b)).card := by
          rw [hL]; exact lt_of_le_of_ne (hbound a') hne
        have hssub : R a' ⊂ (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b) := by
          rw [Finset.ssubset_iff_subset_ne]
          exact ⟨hsub, fun heq => by rw [heq] at hcardlt; exact lt_irrefl _ hcardlt⟩
        obtain ⟨c, hc, hcn⟩ := Finset.exists_of_ssubset hssub
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        refine ⟨c, hc, fun hinj => hcn ?_⟩
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hc, hinj⟩
      by_cases hemp : (R a').Nonempty
      · obtain ⟨b0, hb0⟩ := hemp
        have hanchor : Function.Bijective (fun x => (yK x + a'*xK x, yk x + b0*xk x)) := by
          refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
          · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hb0; exact hb0.2
          · simp only [Fintype.card_prod, ZMod.card]; exact hcard
        exact good_slopes_many_row_fiber_rigidity_conditional_uncolored K k L d xK yK xk yk a' b0 hcard hgap hanchor hbad'
      · rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [hemp]
        simp
    have hsumle : D.sum (fun a' => (R a').card) ≤ r*(L-d) := by
      calc D.sum (fun a' => (R a').card) ≤ D.sum (fun _ => L-d) := Finset.sum_le_sum hle
        _ = D.card * (L-d) := by simp
        _ = r*(L-d) := by rw [hDcard]
    have hmul : r*(L-d) = r*L - r*d := Nat.mul_sub r L d
    rw [hmul] at hsumle
    exact absurd (lt_of_lt_of_le hlarge' hsumle) (lt_irrefl _)
  have hAcard : (R a).card ≤ L - r*d := by
    by_cases hemp : (R a).Nonempty
    · obtain ⟨b0, hb0⟩ := hemp
      have hanchor : Function.Bijective (fun x => (yK x + a*xK x, yk x + b0*xk x)) := by
        refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
        · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hb0; exact hb0.2
        · simp only [Fintype.card_prod, ZMod.card]; exact hcard
      obtain ⟨a1, ha1D, ha1full⟩ := hfull_exists
      have hRequal : R a1 = (Finset.univ : Finset (ZMod k)).filter (fun b => IsUnit b) := by
        apply Finset.eq_of_subset_of_card_le
        · intro c hc
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
          exact hc.1
        · rw [hL, ha1full]
      have hfull : ∀ c : ZMod k, IsUnit c → Function.Injective (fun x => (yK x + a1*xK x, yk x + c*xk x)) := by
        intro c hc
        have hmem : c ∈ R a1 := by rw [hRequal]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem.2
      exact good_slopes_many_row_fiber_rigidity_conditional_colored K k L r d xK yK xk yk a a1 b0 hcard hx hcolored hanchor hfull ⟨b, hb, hcon⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp]
      simp only [Finset.card_empty]
      omega
  have hsplit : D.sum (fun a' => (R a').card) = (D.erase a).sum (fun a' => (R a').card) + (R a).card :=
    (Finset.sum_erase_add D (fun a' => (R a').card) haD).symm
  have herase_card : (D.erase a).card = r - 1 := by
    rw [Finset.card_erase_of_mem haD, hDcard]
  have herase_le : (D.erase a).sum (fun a' => (R a').card) ≤ (r-1)*L := by
    calc (D.erase a).sum (fun a' => (R a').card) ≤ (D.erase a).sum (fun _ => L) := Finset.sum_le_sum (fun a' _ => hbound a')
      _ = (D.erase a).card * L := by simp
      _ = (r-1)*L := by rw [herase_card]
  have hsum_le : D.sum (fun a' => (R a').card) ≤ (r-1)*L + (L - r*d) := by
    rw [hsplit]
    exact add_le_add herase_le hAcard
  have hfin : (r-1)*L + (L - r*d) ≤ r*L - r*d := by
    have hr1 : (r-1)*L + L = r*L := by
      cases r with
      | zero => omega
      | succ s => simp [Nat.succ_mul]
    rw [← hr1, Nat.add_sub_assoc (le_of_lt hLd)]
  exact absurd (lt_of_lt_of_le hlarge' (le_trans hsum_le hfin)) (lt_irrefl _)
