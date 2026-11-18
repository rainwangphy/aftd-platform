import AFTD.Prelude
import AFTD.Kb.Tcs.Op861TriangleOrientation
import AFTD.Kb.Tcs.Op861BinomialPointMassSquareBound
import AFTD.Kb.Tcs.Op861BooleanWeightIntervalCount
import AFTD.Kb.Tcs.Op861DisjointBooleanWindowsCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op861_dense_triangle_orientation_sqrt_cover

Topic: graphs   Node: 05136a6321ba

Provenance: helper lemma. Independent triangle-orientation bottleneck for op861_ternary_tournament_sqrt_core_cover; the related regular-tournament existence is a corollary of arXiv:2608.09728, Lemma 3.4.

There are natural numbers C and n₀ with C positive such that, for every finite linearly ordered abelian group of exponent three with at least n₀ elements, if every half-sized subset has at least one twenty-fourth of the square of the group order many ordered pairs whose zero-sum third point lies outside it, then some choices of cyclic orientations make every half-sized subset contain a vertex whose closed out-neighborhood meets it in at least half of the sum of its size, floor(sqrt(size)/C), and one.
-/

theorem in953_third_ne (α : Type) [AddCommGroup α] (h3 : ∀ t : α, t+t+t = 0)
    (x y : α) (hxy : x ≠ y) : -x-y ≠ x ∧ -x-y ≠ y := by
  have h2 : ∀ t : α, t + t = -t := fun t => eq_neg_of_add_eq_zero_left (h3 t)
  constructor
  · intro h
    apply hxy
    have : y = -(x + (-x-y)) := by abel
    rw [this, h, h2, neg_neg]
  · intro h
    apply hxy
    have : x = -(y + (-x-y)) := by abel
    rw [this, h, h2, neg_neg]

theorem in953_cyc_swap (α : Type) [LinearOrder α] (a b c : α)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ((b < a ∧ a < c) ∨ (a < c ∧ c < b) ∨ (c < b ∧ b < a)) ↔
      ¬ ((a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h4 | h4 <;>
    simp only [h1, h2, h4, not_lt_of_gt, true_and, and_true, false_and, and_false,
      or_false, false_or, true_or, or_true, not_true, not_false_eq_true]

theorem in953_antisymm (α : Type) [AddCommGroup α] [DecidableEq α] [LinearOrder α]
    (h3 : ∀ t : α, t+t+t = 0) (turn : Finset α → Bool) (x y : α) (hxy : x ≠ y) :
    op861_triangle_orientation α turn x y = true ↔ op861_triangle_orientation α turn y x = false := by
  obtain ⟨h1, h2⟩ := in953_third_ne α h3 x y hxy
  have hz : -y-x = -x-y := by abel
  have hs : ({y, x, -y-x} : Finset α) = {x, y, -x-y} := by
    rw [hz, Finset.insert_comm]
  have hc := in953_cyc_swap α x y (-x-y) hxy (Ne.symm h2) (Ne.symm h1)
  unfold op861_triangle_orientation
  rw [hs, hz]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  rw [hc]
  cases turn {x, y, -x-y} <;>
    simp only [hxy, Ne.symm hxy, ne_eq, not_false_eq_true, true_and, Bool.false_eq_true,
      false_iff, true_iff, not_not, iff_self]

theorem in953_cyclic (α : Type) [AddCommGroup α] [DecidableEq α] [LinearOrder α]
    (h3 : ∀ t : α, t+t+t = 0) (turn : Finset α → Bool) (x y : α) (hxy : x ≠ y) :
    op861_triangle_orientation α turn x y = op861_triangle_orientation α turn y (-x-y) := by
  obtain ⟨h1, h2⟩ := in953_third_ne α h3 x y hxy
  have hz : -y-(-x-y) = x := by abel
  have hs : ({y, -x-y, -y-(-x-y)} : Finset α) = {x, y, -x-y} := by
    rw [hz]; ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  unfold op861_triangle_orientation
  rw [hs, hz]
  simp only [ne_eq, hxy, Ne.symm h2, not_false_eq_true, true_and]
  congr 2
  apply propext
  constructor <;> intro h <;> rcases h with h | h | h <;> simp_all

theorem in953_out_iff (α : Type) [AddCommGroup α] [DecidableEq α] [LinearOrder α]
    (h3 : ∀ t : α, t+t+t = 0) (turn : Finset α → Bool) (x y : α) (hxy : x ≠ y) :
    op861_triangle_orientation α turn x y = true ↔
      op861_triangle_orientation α turn x (-x-y) = false := by
  obtain ⟨h1, h2⟩ := in953_third_ne α h3 x y hxy
  rw [in953_cyclic α h3 turn x y hxy, in953_cyclic α h3 turn y (-x-y) (Ne.symm h2)]
  have hz : -y-(-x-y) = x := by abel
  rw [hz]
  exact in953_antisymm α h3 turn (-x-y) x h1

theorem in953_self (α : Type) [AddCommGroup α] [DecidableEq α] [LinearOrder α]
    (turn : Finset α → Bool) (x : α) : op861_triangle_orientation α turn x x = false := by
  unfold op861_triangle_orientation; simp

theorem in953_regular (α : Type) [AddCommGroup α] [Fintype α] [DecidableEq α] [LinearOrder α]
    (h3 : ∀ t : α, t+t+t = 0) (turn : Finset α → Bool) (x : α) :
    2 * (Finset.univ.filter (fun y => op861_triangle_orientation α turn x y = true)).card + 1
      = Fintype.card α := by
  set O := Finset.univ.filter (fun y => op861_triangle_orientation α turn x y = true)
  set I := Finset.univ.filter (fun y => y ≠ x ∧ op861_triangle_orientation α turn x y = false)
  have hOI : O.card = I.card := by
    apply Finset.card_bij (fun y _ => -x-y)
    · intro y hy
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hyx : x ≠ y := by rintro rfl; rw [in953_self] at hy; exact absurd hy (by simp)
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(in953_third_ne α h3 x y hyx).1, (in953_out_iff α h3 turn x y hyx).1 hy⟩
    · intro a _ b _ h
      have : a = -x - (-x-a) := by abel
      rw [this, h]; abel
    · intro z hz
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have hxz : x ≠ z := Ne.symm hz.1
      have hy : -x-z ≠ x := (in953_third_ne α h3 x z hxz).1
      refine ⟨-x-z, ?_, by abel⟩
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [in953_out_iff α h3 turn x (-x-z) (Ne.symm hy)]
      have : -x-(-x-z) = z := by abel
      rw [this]; exact hz.2
  have hdisj : Disjoint O I := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [O, I, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    rw [hy] at hy'; exact absurd hy'.2 (by simp)
  have hunion : O ∪ I = Finset.univ.erase x := by
    ext y
    simp only [O, I, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (h | h)
      · rintro rfl; rw [in953_self] at h; exact absurd h (by simp)
      · exact h.1
    · intro h
      cases hb : op861_triangle_orientation α turn x y
      · exact Or.inr ⟨h, rfl⟩
      · exact Or.inl rfl
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at this
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
  omega

theorem in953_block_facts (α : Type) [AddCommGroup α] [DecidableEq α]
    (S A : Finset α) (hAS : A ⊆ S) (x : α) (hx : x ∈ A) :
    (∀ y ∈ (S \ A).filter (fun y => -(x+y) ∉ S), y ≠ x ∧ y ∈ S ∧ -x-y ∉ S) ∧
    (∀ y ∈ (S \ A).filter (fun y => -(x+y) ∉ S), ∀ y' ∈ (S \ A).filter (fun y => -(x+y) ∉ S),
      ({x, y, -x-y} : Finset α) = {x, y', -x-y'} → y = y') := by
  have hn : ∀ a b : α, -a-b = -(a+b) := fun a b => by abel
  have f1 : ∀ y ∈ (S \ A).filter (fun y => -(x+y) ∉ S), y ≠ x ∧ y ∈ S ∧ -x-y ∉ S := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hy
    refine ⟨?_, hy.1.1, by rw [hn]; exact hy.2⟩
    rintro rfl; exact hy.1.2 hx
  refine ⟨f1, ?_⟩
  intro y hy y' hy' h
  obtain ⟨a1, a2, a3⟩ := f1 y hy
  obtain ⟨b1, b2, b3⟩ := f1 y' hy'
  have : y' ∈ ({x, y, -x-y} : Finset α) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h1 | h1 | h1
  · exact absurd h1 b1
  · exact h1.symm
  · rw [h1] at b2; exact absurd b2 a3

theorem in953_block_count (α : Type) [AddCommGroup α] [Fintype α] [DecidableEq α]
    [LinearOrder α] (h3 : ∀ t : α, t+t+t = 0)
    (S A T : Finset α) (hAS : A ⊆ S) (hTA : T ⊆ A) (k w : ℕ)
    (hY : ∀ x ∈ T, k ≤ 96 * ((S \ A).filter (fun y => -(x+y) ∉ S)).card)
    (lo hi : ℤ) (hlh : lo ≤ hi) (hw : (hi - lo + 1).toNat ≤ w) :
    ((Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ T,
        lo ≤ ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ∧
        ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ≤ hi)).card ^ 2
      * k ^ T.card ≤ (2 ^ Fintype.card (Finset α)) ^ 2 * (192 * w^2) ^ T.card := by
  classical
  have hn : ∀ a b : α, -a-b = -(a+b) := fun a b => by abel
  set Y : α → Finset α := fun x => (S \ A).filter (fun y => -(x+y) ∉ S) with hYdef
  set line : α → α → Finset α := fun x y => ({x, y, -x-y} : Finset α) with hline
  set B : α → Finset (Finset α) := fun x => (Y x).image (line x) with hB
  set pattern : α → Finset α → Bool := fun x t => decide (∃ y ∈ Y x, t = line x y ∧
      ((x < y ∧ y < -x-y) ∨ (y < -x-y ∧ -x-y < x) ∨ (-x-y < x ∧ x < y))) with hpat
  set offset : α → (Finset α → Bool) → ℤ := fun x ω =>
      (((S \ Y x).filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) with hoff
  have hfacts : ∀ x ∈ T, _ := fun x hx => in953_block_facts α S A hAS x (hTA hx)
  -- f3
  have f3 : ∀ x ∈ T, ∀ y ∈ Y x, ∀ ω : Finset α → Bool,
      (op861_triangle_orientation α ω x y = true ↔ ω (line x y) = pattern x (line x y)) := by
    intro x hx y hy ω
    obtain ⟨f1, f2⟩ := hfacts x hx
    have hyx := (f1 y hy).1
    have hpe : pattern x (line x y) = decide ((x < y ∧ y < -x-y) ∨ (y < -x-y ∧ -x-y < x) ∨ (-x-y < x ∧ x < y)) := by
      simp only [hpat]
      congr 1
      apply propext
      constructor
      · rintro ⟨y', hy', he, hc⟩
        have := f2 y hy y' hy' he
        subst this; exact hc
      · intro hc; exact ⟨y, hy, rfl, hc⟩
    rw [hpe]
    unfold op861_triangle_orientation
    simp only [hline, decide_eq_true_eq, ne_eq, Ne.symm hyx, not_false_eq_true, true_and]
    cases ω {x, y, -x-y} <;> simp
  -- f4 split
  have f4 : ∀ x ∈ T, ∀ ω : Finset α → Bool,
      ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) =
        offset x ω + ∑ t ∈ B x, (if ω t = pattern x t then (1:ℤ) else 0) := by
    intro x hx ω
    obtain ⟨f1, f2⟩ := hfacts x hx
    have hYS : Y x ⊆ S := fun y hy => (f1 y hy).2.1
    have hsplit : S.filter (fun y => op861_triangle_orientation α ω x y = true) =
        (S \ Y x).filter (fun y => op861_triangle_orientation α ω x y = true) ∪
        (Y x).filter (fun y => op861_triangle_orientation α ω x y = true) := by
      rw [← Finset.filter_union, Finset.sdiff_union_of_subset hYS]
    have hdisj : Disjoint ((S \ Y x).filter (fun y => op861_triangle_orientation α ω x y = true))
        ((Y x).filter (fun y => op861_triangle_orientation α ω x y = true)) :=
      Finset.disjoint_filter_filter Finset.sdiff_disjoint
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
    congr 1
    rw [Finset.sum_image (fun y hy y' hy' h => f2 y hy y' hy' h)]
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have := f3 x hx y hy ω
    by_cases h : op861_triangle_orientation α ω x y = true
    · rw [if_pos h, if_pos (this.1 h)]; simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
  -- disjointness
  have f5 : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (B i) (B j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [hB, Finset.mem_image] at ht ht'
    obtain ⟨y, hy, rfl⟩ := ht
    obtain ⟨y', hy', he⟩ := ht'
    obtain ⟨f1, _⟩ := hfacts j hj
    obtain ⟨b1, b2, b3⟩ := f1 y' hy'
    have : i ∈ line j y' := by rw [he]; simp [hline]
    simp only [hline, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact hij h1
    · have : y' ∈ Y j := hy'
      simp only [hYdef, Finset.mem_filter, Finset.mem_sdiff] at this
      rw [← h1] at this; exact this.1.2 (hTA hi)
    · rw [← h1] at b3; exact b3 (hAS (hTA hi))
  -- stability
  have f6 : ∀ i ∈ T, ∀ ω ω' : Finset α → Bool,
      (∀ t, t ∉ T.biUnion B → ω t = ω' t) → offset i ω = offset i ω' := by
    intro i hi ω ω' hagree
    simp only [hoff]
    congr 2
    apply Finset.filter_congr
    intro y hy
    by_cases hyi : y = i
    · subst hyi; unfold op861_triangle_orientation; simp
    have hnot : line i y ∉ T.biUnion B := by
      intro hm
      simp only [Finset.mem_biUnion, hB, Finset.mem_image] at hm
      obtain ⟨j, hj, y', hy', he⟩ := hm
      obtain ⟨f1, _⟩ := hfacts j hj
      obtain ⟨b1, b2, b3⟩ := f1 y' hy'
      simp only [Finset.mem_sdiff] at hy
      have hiS : i ∈ S := hAS (hTA hi)
      have : i ∈ line j y' := by rw [he]; simp [hline]
      simp only [hline, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h1 | h1
      · subst h1
        have : y ∈ line i y' := by rw [he]; simp [hline]
        simp only [hline, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h2 | h2 | h2
        · exact hyi h2
        · exact hy.2 (h2 ▸ hy')
        · exact b3 (h2 ▸ hy.1)
      · have : y' ∈ Y j := hy'
        simp only [hYdef, Finset.mem_filter, Finset.mem_sdiff] at this
        rw [← h1] at this; exact this.1.2 (hTA hi)
      · exact b3 (h1 ▸ hiS)
    unfold op861_triangle_orientation
    rw [hagree _ hnot]
  have hwin := op861_disjoint_boolean_windows_count (Finset α) α T B pattern
    (fun _ => lo) (fun _ => hi) offset f5 (fun _ _ => hlh) f6
  dsimp only at hwin
  have hset : (Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ T,
        lo ≤ ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ∧
        ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ≤ hi) =
      (Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ i ∈ T,
        lo ≤ offset i ω + ∑ t ∈ B i, (if ω t = pattern i t then (1:ℤ) else 0) ∧
        offset i ω + ∑ t ∈ B i, (if ω t = pattern i t then (1:ℤ) else 0) ≤ hi) := by
    apply Finset.filter_congr
    intro ω _
    constructor
    · intro h i hi; rw [← f4 i hi ω]; exact h i hi
    · intro h i hi; rw [f4 i hi ω]; exact h i hi
  set gcnt := ((Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ T,
        lo ≤ ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ∧
        ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ≤ hi)).card
  set N := 2 ^ Fintype.card (Finset α)
  have hbY : ∀ i ∈ T, (B i).card = (Y i).card := by
    intro i hi
    exact Finset.card_image_of_injOn (fun y hy y' hy' h => (hfacts i hi).2 y hy y' hy' h)
  set P := ∏ i ∈ T, 2 ^ (B i).card
  set Q := ∏ i ∈ T, (B i).card.choose ((B i).card / 2)
  set R := ∏ i ∈ T, ((B i).card + 1)
  have hwin' : gcnt * P ≤ N * ∏ i ∈ T, ((hi - lo + 1).toNat * (B i).card.choose ((B i).card / 2)) := by
    simp only [gcnt, P, N]; rw [hset]; convert hwin using 3 <;> (ext ω; simp only [Finset.mem_filter])
  have h1 : gcnt * P ≤ N * (w ^ T.card * Q) := by
    refine hwin'.trans (Nat.mul_le_mul_left _ ?_)
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' (fun i _ => Nat.mul_le_mul_right _ hw)
  have h2 : R * Q ^ 2 ≤ 2 ^ T.card * P ^ 2 := by
    simp only [R, Q, P, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod' (fun i _ => ?_)
    have := op861_binomial_point_mass_square_bound (B i).card ((B i).card / 2)
    calc ((B i).card + 1) * (B i).card.choose ((B i).card / 2) ^ 2 ≤ 2 * 4 ^ (B i).card := this
      _ = 2 * (2 ^ (B i).card) ^ 2 := by rw [← pow_mul, mul_comm (B i).card 2, pow_mul]; norm_num
  have h3' : k ^ T.card ≤ 96 ^ T.card * R := by
    rw [← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod' (fun i hi => ?_)
    have := hY i hi
    rw [hbY i hi]
    have : (Y i).card = ((S \ A).filter (fun y => -(i+y) ∉ S)).card := rfl
    nlinarith
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => by positivity)
  have h4 : gcnt ^ 2 * R * P ^ 2 ≤ N ^ 2 * (w ^ T.card) ^ 2 * 2 ^ T.card * P ^ 2 := by
    have hsq : (gcnt * P) ^ 2 ≤ (N * (w ^ T.card * Q)) ^ 2 := Nat.pow_le_pow_left h1 2
    calc gcnt ^ 2 * R * P ^ 2 = R * (gcnt * P) ^ 2 := by ring
      _ ≤ R * (N * (w ^ T.card * Q)) ^ 2 := Nat.mul_le_mul_left _ hsq
      _ = N ^ 2 * (w ^ T.card) ^ 2 * (R * Q ^ 2) := by ring
      _ ≤ N ^ 2 * (w ^ T.card) ^ 2 * (2 ^ T.card * P ^ 2) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  have h5 : gcnt ^ 2 * R ≤ N ^ 2 * (w ^ T.card) ^ 2 * 2 ^ T.card :=
    Nat.le_of_mul_le_mul_right h4 (by positivity)
  calc gcnt ^ 2 * k ^ T.card ≤ gcnt ^ 2 * (96 ^ T.card * R) := Nat.mul_le_mul_left _ h3'
    _ = 96 ^ T.card * (gcnt ^ 2 * R) := by ring
    _ ≤ 96 ^ T.card * (N ^ 2 * (w ^ T.card) ^ 2 * 2 ^ T.card) := Nat.mul_le_mul_left _ h5
    _ = N ^ 2 * (192 * w ^ 2) ^ T.card := by
      rw [show (192:ℕ) * w^2 = 96 * 2 * w^2 by norm_num, mul_pow, mul_pow]; ring

theorem in953_select (α : Type) [AddCommGroup α] [DecidableEq α] (S : Finset α) (k : ℕ)
    (hk : S.card = k)
    (hP : k^2 ≤ 24 * ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card) :
    ∃ A ⊆ S, A.card = k / 96 ∧ ∀ x ∈ A, k ≤ 96 * ((S \ A).filter (fun y => -(x+y) ∉ S)).card := by
  classical
  set deg : α → ℕ := fun x => (S.filter (fun y => -(x+y) ∉ S)).card with hdeg
  have hPsum : ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card = ∑ x ∈ S, deg x := by
    rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hdeg, Finset.card_filter]
  set H := S.filter (fun x => k ≤ 48 * deg x) with hH
  have hdegle : ∀ x, deg x ≤ k := fun x => hk ▸ Finset.card_filter_le _ _
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => k ≤ 48 * deg x) deg
  have hA1 : ∑ x ∈ H, deg x ≤ H.card * k := by
    have := Finset.sum_le_card_nsmul H deg k (fun x _ => hdegle x)
    simpa using this
  have hA2 : 48 * ∑ x ∈ S.filter (fun x => ¬ k ≤ 48 * deg x), deg x ≤ k * k := by
    rw [Finset.mul_sum]
    have := Finset.sum_le_card_nsmul (S.filter (fun x => ¬ k ≤ 48 * deg x)) (fun x => 48 * deg x) k
      (fun x hx => by simp only [Finset.mem_filter] at hx; omega)
    have hc : (S.filter (fun x => ¬ k ≤ 48 * deg x)).card ≤ k := hk ▸ Finset.card_filter_le _ _
    simp only [smul_eq_mul] at this
    calc _ ≤ _ := this
      _ ≤ k * k := Nat.mul_le_mul_right _ hc
  have hHk : k ≤ 48 * H.card := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · omega
    have : k * k ≤ 48 * H.card * k := by
      have h0 := hP
      rw [hPsum, ← hsplit, sq, ← hH] at h0
      linarith
    exact Nat.le_of_mul_le_mul_right (by linarith) hpos
  obtain ⟨A, hAH, hAc⟩ := Finset.exists_subset_card_eq (s := H) (n := k / 96) (by omega)
  refine ⟨A, hAH.trans (Finset.filter_subset _ _), hAc, ?_⟩
  intro x hx
  have hxH := hAH hx
  simp only [hH, Finset.mem_filter] at hxH
  have hsub : (S.filter (fun y => -(x+y) ∉ S)) \ A ⊆ (S \ A).filter (fun y => -(x+y) ∉ S) := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hy ⊢
    tauto
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.le_card_sdiff A (S.filter (fun y => -(x+y) ∉ S))
  have h3 : deg x = (S.filter (fun y => -(x+y) ∉ S)).card := rfl
  omega

theorem in953_sum_scores (α : Type) [AddCommGroup α] [DecidableEq α] [LinearOrder α]
    (h3 : ∀ t : α, t+t+t = 0) (ω : Finset α → Bool) (S : Finset α) :
    ∑ x ∈ S, 2 * (S.filter (fun y => op861_triangle_orientation α ω x y = true)).card + S.card
      = S.card * S.card := by
  set f : α → α → ℕ := fun x y => if op861_triangle_orientation α ω x y = true then 1 else 0
  have hc : ∀ x, (S.filter (fun y => op861_triangle_orientation α ω x y = true)).card =
      ∑ y ∈ S, f x y := fun x => Finset.card_filter _ _
  have hpair : ∀ x y, f x y + f y x + (if y = x then 1 else 0) = 1 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp [f, in953_self]
    · have := in953_antisymm α h3 ω x y hxy
      simp only [f, if_neg (Ne.symm hxy)]
      cases h : op861_triangle_orientation α ω x y <;> simp_all
  have hrow : ∀ x ∈ S, ∑ y ∈ S, (f x y + f y x) + 1 = S.card := by
    intro x hx
    have := Finset.sum_congr rfl (fun y (_ : y ∈ S) => hpair x y)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S x, if_pos hx] at this
    simpa using this
  have hcomm : ∑ x ∈ S, ∑ y ∈ S, f y x = ∑ x ∈ S, ∑ y ∈ S, f x y := Finset.sum_comm
  simp only [hc]
  have : ∑ x ∈ S, (∑ y ∈ S, (f x y + f y x) + 1) = ∑ x ∈ S, S.card :=
    Finset.sum_congr rfl hrow
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_const, smul_eq_mul] at this
  simp only [Finset.sum_add_distrib, hcomm] at this
  rw [← Finset.mul_sum]
  linarith

theorem in953_insert_card (α : Type) [AddCommGroup α] [Fintype α] [DecidableEq α] [LinearOrder α]
    (ω : Finset α → Bool) (S : Finset α) (x : α) (hx : x ∈ S) :
    (S ∩ insert x (Finset.univ.filter (fun y => op861_triangle_orientation α ω x y = true))).card
      = (S.filter (fun y => op861_triangle_orientation α ω x y = true)).card + 1 := by
  have : S ∩ insert x (Finset.univ.filter (fun y => op861_triangle_orientation α ω x y = true))
      = insert x (S.filter (fun y => op861_triangle_orientation α ω x y = true)) := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h1, h2⟩
    · rintro (h | h)
      · subst h; exact ⟨hx, Or.inl rfl⟩
      · exact ⟨h.1, Or.inr h.2⟩
  rw [this, Finset.card_insert_of_notMem]
  simp [in953_self]

theorem in953_bad_bound (α : Type) [AddCommGroup α] [Fintype α] [DecidableEq α]
    [LinearOrder α] (h3 : ∀ t : α, t+t+t = 0) (S : Finset α) (k s G : ℕ) (hk : S.card = k)
    (hP : k^2 ≤ 24 * ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card)
    (hG : ∀ gcnt : ℕ, gcnt ^ 2 * k ^ (k/96 - k/96/2) ≤
      (2 ^ Fintype.card (Finset α)) ^ 2 * (192 * (192 * s + 2)^2) ^ (k/96 - k/96/2) → gcnt ≤ G) :
    ((Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ S,
      2 * (S ∩ insert x (Finset.univ.filter
        (fun y => op861_triangle_orientation α ω x y = true))).card < k + s + 1)).card
      ≤ 2 ^ (k/96) * G := by
  classical
  obtain ⟨A, hAS, hAc, hAY⟩ := in953_select α S k hk hP
  set m := k / 96 with hm
  set j := m - m / 2 with hj
  set lo : ℤ := ((k:ℤ) + s - 2 - 192 * s) / 2 with hlo
  set hi : ℤ := ((k:ℤ) + s - 2) / 2 with hhi
  set Good : Finset α → Finset (Finset α → Bool) := fun T =>
    (Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ T,
        lo ≤ ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ∧
        ((S.filter (fun y => op861_triangle_orientation α ω x y = true)).card : ℤ) ≤ hi) with hGood
  have hsub : (Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ S,
      2 * (S ∩ insert x (Finset.univ.filter
        (fun y => op861_triangle_orientation α ω x y = true))).card < k + s + 1) ⊆
      (A.powersetCard j).biUnion Good := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    set sc : α → ℕ := fun x => (S.filter (fun y => op861_triangle_orientation α ω x y = true)).card
      with hsc
    have hb : ∀ x ∈ S, 2 * sc x + 2 ≤ k + s := by
      intro x hx
      have := hω x hx
      rw [in953_insert_card α ω S x hx] at this
      simp only [hsc]; omega
    have hsum := in953_sum_scores α h3 ω S
    rw [hk] at hsum
    set f : α → ℕ := fun x => k + s - (2 * sc x + 2) with hf
    have hfsum : ∑ x ∈ S, f x + k = k * s := by
      have e : ∀ x ∈ S, f x + (2 * sc x + 2) = k + s := by
        intro x hx; have := hb x hx; simp only [hf]; omega
      have := Finset.sum_congr rfl e
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul, hk] at this
      have hsum' : ∑ x ∈ S, 2 * sc x + k = k * k := hsum
      nlinarith
    set Fbig := A.filter (fun x => 192 * s < f x) with hFbig
    have hFle : Fbig.card ≤ m / 2 := by
      by_contra hcon
      push_neg at hcon
      have h1 : Fbig.card * (192 * s + 1) ≤ ∑ x ∈ Fbig, f x := by
        have := Finset.card_nsmul_le_sum Fbig f (192 * s + 1) (fun x hx => by
          simp only [hFbig, Finset.mem_filter] at hx; omega)
        simpa using this
      have h2 : ∑ x ∈ Fbig, f x ≤ ∑ x ∈ S, f x :=
        Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans hAS)
      have h3' : k ≤ 192 * (m / 2 + 1) := by omega
      have h4 : (m / 2 + 1) * (192 * s + 1) ≤ Fbig.card * (192 * s + 1) :=
        Nat.mul_le_mul_right _ hcon
      have h5 : k * s ≤ 192 * (m / 2 + 1) * s := Nat.mul_le_mul_right s h3'
      generalize m / 2 = q at h4 h5
      have h6 : (q + 1) * (192 * s + 1) = 192 * (q + 1) * s + (q + 1) := by ring
      linarith
    have hFA : Fbig ⊆ A := Finset.filter_subset _ _
    have hcard : j ≤ (A \ Fbig).card := by
      rw [Finset.card_sdiff_of_subset hFA]; omega
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard]
    refine ⟨T, ⟨hT.trans Finset.sdiff_subset, hTc⟩, ?_⟩
    simp only [hGood, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    have hxA : x ∈ A := (Finset.sdiff_subset (hT hx))
    have hxF : x ∉ Fbig := (Finset.mem_sdiff.mp (hT hx)).2
    simp only [hFbig, Finset.mem_filter, not_and, not_lt] at hxF
    have e1 := hxF hxA
    have e2 := hb x (hAS hxA)
    simp only [hf, hsc] at e1 e2
    constructor <;> omega
  have hGoodle : ∀ T ∈ A.powersetCard j, (Good T).card ≤ G := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    apply hG
    have := in953_block_count α h3 S A T hAS hT.1 k (192 * s + 2) (fun x hx => hAY x (hT.1 hx))
      lo hi (by omega) (by omega)
    rw [hT.2] at this
    exact this
  calc _ ≤ ((A.powersetCard j).biUnion Good).card := Finset.card_le_card hsub
    _ ≤ ∑ T ∈ A.powersetCard j, (Good T).card := Finset.card_biUnion_le
    _ ≤ (A.powersetCard j).card * G := by
        have := Finset.sum_le_card_nsmul _ _ G hGoodle
        simpa using this
    _ ≤ 2 ^ m * G := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_powersetCard, hAc]
        exact Nat.choose_le_two_pow _ _

theorem in953_numeric (n k E : ℕ) (hE : 1000 ≤ E) (hk : (2 ^ E) ^ 2 ≤ k) (hbig : 2375 ≤ k)
    (hn : n + 1 = 2 * k) :
    4 ^ n * 4 ^ (k/96) * (192 * (192 * (Nat.sqrt k / 2 ^ E) + 2) ^ 2) ^ (k/96 - k/96/2)
      < k ^ (k/96 - k/96/2) := by
  generalize hCdef : (2 : ℕ) ^ E = C at hk ⊢
  have hCpos : 0 < C := by rw [← hCdef]; positivity
  set s := Nat.sqrt k / C with hs
  set m := k / 96 with hm
  set j := m - m / 2 with hj
  have hsq : C ≤ Nat.sqrt k := Nat.le_sqrt'.mpr hk
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_div_iff_mul_le hCpos]; omega
  have hsC : s * C ≤ Nat.sqrt k := by rw [hs]; exact Nat.div_mul_le_self _ _
  have hsC2 : (s * C) ^ 2 ≤ k := (Nat.pow_le_pow_left hsC 2).trans (Nat.sqrt_le' k)
  have hexp : 2 * n + 2 * m + 23 * j < 2000 * j := by omega
  have hexp2 : 2000 * j ≤ (2 * E) * j := Nat.mul_le_mul_right j (by omega)
  have hw : (192 * (192 * s + 2) ^ 2) * C ^ 2 ≤ 2 ^ 23 * k := by
    have h1 : 192 * s + 2 ≤ 194 * s := by omega
    have h2 : (192 * s + 2) ^ 2 ≤ (194 * s) ^ 2 := Nat.pow_le_pow_left h1 2
    calc (192 * (192 * s + 2) ^ 2) * C ^ 2 ≤ (192 * (194 * s) ^ 2) * C ^ 2 := by gcongr
      _ = 192 * 194 ^ 2 * (s * C) ^ 2 := by ring
      _ ≤ 2 ^ 23 * (s * C) ^ 2 := by gcongr; norm_num
      _ ≤ 2 ^ 23 * k := by gcongr
  have hkpos : 0 < k ^ j := by positivity
  have key : 4 ^ n * 4 ^ m * (192 * (192 * s + 2) ^ 2) ^ j * (C ^ 2) ^ j < k ^ j * (C ^ 2) ^ j := by
    calc 4 ^ n * 4 ^ m * (192 * (192 * s + 2) ^ 2) ^ j * (C ^ 2) ^ j
        = 4 ^ n * 4 ^ m * ((192 * (192 * s + 2) ^ 2) * C ^ 2) ^ j := by rw [mul_pow (192 * (192 * s + 2) ^ 2) (C ^ 2) j]; ring
      _ ≤ 4 ^ n * 4 ^ m * (2 ^ 23 * k) ^ j := by gcongr
      _ = 2 ^ (2 * n + 2 * m + 23 * j) * k ^ j := by
          rw [mul_pow, pow_add, pow_add, pow_mul, pow_mul, pow_mul]; norm_num; ring
      _ < 2 ^ ((2 * E) * j) * k ^ j := by
          apply Nat.mul_lt_mul_of_pos_right _ hkpos
          exact Nat.pow_lt_pow_right (by norm_num) (lt_of_lt_of_le hexp hexp2)
      _ = k ^ j * (C ^ 2) ^ j := by rw [← hCdef, ← pow_mul, ← pow_mul, show 2 * E * j = E * (2 * j) by ring]; ring
  exact Nat.lt_of_mul_lt_mul_right key

theorem op861_dense_triangle_orientation_sqrt_cover :
    ∃ C n₀ : ℕ, 0 < C ∧
      ∀ (α : Type) [AddCommGroup α] [Fintype α] [DecidableEq α] [LinearOrder α],
        n₀ ≤ Fintype.card α → (∀ t : α, t+t+t = 0) →
        (∀ S : Finset α, 2 * S.card = Fintype.card α + 1 →
          (Fintype.card α)^2 ≤ 24 * ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card) →
        ∃ turn : Finset α → Bool, ∀ S : Finset α,
          2 * S.card = Fintype.card α + 1 → ∃ x ∈ S,
            S.card + Nat.sqrt S.card / C + 1 ≤
              2 * (S ∩ insert x (Finset.univ.filter (fun y => op861_triangle_orientation α turn x y = true))).card := by
  refine ⟨2 ^ 1000, 2 ^ 2001, by positivity, ?_⟩
  intro α _ _ _ _ hn h3 hcross
  classical
  have h12 : (2375 : ℕ) ≤ 2 ^ 2000 :=
    le_trans (by norm_num : (2375:ℕ) ≤ 2 ^ 12) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hpw : (2 ^ 1000 : ℕ) ^ 2 = 2 ^ 2000 := by rw [← pow_mul]
  have hpw2 : (2 : ℕ) ^ 2001 = 2 * 2 ^ 2000 := by rw [pow_succ]; ring
  set n := Fintype.card α with hndef
  set k := (n + 1) / 2 with hkdef
  have hk2 : (2 ^ 1000) ^ 2 ≤ k := by
    rw [hpw]; rw [hpw2] at hn; generalize (2:ℕ) ^ 2000 = X at hn ⊢; omega
  have hbig : 2375 ≤ k := by
    have h := hk2; rw [hpw] at h; exact le_trans h12 h
  by_cases hodd : n + 1 = 2 * k
  swap
  · refine ⟨fun _ => false, fun S hS => ?_⟩
    exfalso; omega
  set s := Nat.sqrt k / 2 ^ 1000 with hs
  set m := k / 96 with hm
  set j := m - m / 2 with hj
  set N := 2 ^ Fintype.card (Finset α) with hN
  set M := N ^ 2 * (192 * (192 * s + 2) ^ 2) ^ j with hM
  have hkj : 0 < k ^ j := pow_pos (by omega) j
  set G := Nat.sqrt (M / k ^ j) with hGdef
  have hG : ∀ gcnt : ℕ, gcnt ^ 2 * k ^ j ≤ M → gcnt ≤ G := by
    intro gcnt hg
    rw [hGdef]
    apply Nat.le_sqrt'.mpr
    exact (Nat.le_div_iff_mul_le hkj).mpr hg
  have hGM : G ^ 2 * k ^ j ≤ M :=
    le_trans (Nat.mul_le_mul_right _ (Nat.sqrt_le' _)) (Nat.div_mul_le_self _ _)
  have hnum := in953_numeric n k 1000 le_rfl hk2 hbig hodd
  set I := (Finset.univ : Finset (Finset α)).filter (fun S => 2 * S.card = n + 1) with hI
  set Bad : Finset α → Finset (Finset α → Bool) := fun S =>
    (Finset.univ : Finset (Finset α → Bool)).filter (fun ω => ∀ x ∈ S,
      2 * (S ∩ insert x (Finset.univ.filter
        (fun y => op861_triangle_orientation α ω x y = true))).card < k + s + 1) with hBad
  have hBadle : ∀ S ∈ I, (Bad S).card ≤ 2 ^ m * G := by
    intro S hS
    simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hSk : S.card = k := by omega
    have hP : k ^ 2 ≤ 24 * ((S.product S).filter (fun xy => -(xy.1+xy.2) ∉ S)).card := by
      have := hcross S hS
      have hkn : k ≤ n := by omega
      exact le_trans (Nat.pow_le_pow_left hkn 2) this
    exact in953_bad_bound α h3 S k s G hSk hP hG
  have hIcard : I.card ≤ 2 ^ n := by
    calc I.card ≤ (Finset.univ : Finset (Finset α)).card := Finset.card_filter_le _ _
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset]
  have hlt : 2 ^ n * (2 ^ m * G) < N := by
    have h1 : (2 ^ n * (2 ^ m * G)) ^ 2 * k ^ j < N ^ 2 * k ^ j := by
      calc (2 ^ n * (2 ^ m * G)) ^ 2 * k ^ j = 4 ^ n * 4 ^ m * (G ^ 2 * k ^ j) := by
            rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
        _ ≤ 4 ^ n * 4 ^ m * M := Nat.mul_le_mul_left _ hGM
        _ = N ^ 2 * (4 ^ n * 4 ^ m * (192 * (192 * s + 2) ^ 2) ^ j) := by rw [hM]; ring
        _ < N ^ 2 * k ^ j := Nat.mul_lt_mul_of_pos_left hnum (by positivity)
    have h2 := Nat.lt_of_mul_lt_mul_right h1
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hcardU : (I.biUnion Bad).card < (Finset.univ : Finset (Finset α → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
    calc (I.biUnion Bad).card ≤ ∑ S ∈ I, (Bad S).card := Finset.card_biUnion_le
      _ ≤ I.card * (2 ^ m * G) := by
          have := Finset.sum_le_card_nsmul I _ _ hBadle
          simpa using this
      _ ≤ 2 ^ n * (2 ^ m * G) := Nat.mul_le_mul_right _ hIcard
      _ < N := hlt
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardU
  refine ⟨ω, fun S hS => ?_⟩
  have hSI : S ∈ I := by simp [hI, hS]
  have hSk : S.card = k := by omega
  have hnot : ω ∉ Bad S := fun h => hω (Finset.mem_biUnion.mpr ⟨S, hSI, h⟩)
  simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_lt] at hnot
  obtain ⟨x, hx, hle⟩ := hnot
  exact ⟨x, hx, by rw [hSk]; exact hle⟩
