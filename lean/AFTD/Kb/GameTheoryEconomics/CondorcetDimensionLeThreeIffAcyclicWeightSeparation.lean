import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.CondorcetFailureIffAcyclicHalfCover
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.G

/-!
# condorcet_dimension_le_three_iff_acyclic_weight_separation

Topic: social_choice   Node: 97628117a4b8

Provenance: helper lemma. IN-357 supporting reformulation for OP-19. Strict definition: Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Uses the proved condorcet_failure_iff_acyclic_half_cover bridge. Standard fractional acyclic-cover duality is discussed in https://dmtcs.episciences.org/6020/pdf and https://arxiv.org/abs/2609.35186 . The proof includes the finite rational/integer conversion, so real convex separation adds no hidden existence assumption. This is formal infrastructure, not a new election bound or a research advance.

The following two universal statements are equivalent. First, every finite election with a positive number of voters and strict rankings has a strict Condorcet winning set of at most three candidates. Second, for every finite directed relation such that every set of at most three vertices has an outside common predecessor, there are nonnegative real vertex weights such that every induced acyclic vertex subset has weight strictly less than half the total vertex weight. Acyclicity on finite sets is expressed by WellFounded of the restricted relation. Both sides remain universal existence claims; the equivalence supplies neither a weight construction nor a counterexample.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_finite_weighted_half_cover_exclusion
    (m n : ℕ) (hn : 0 < n)
    (U : Fin n → Finset (Fin m))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsep : ∀ v, 2 * (∑ a ∈ U v, w a) < ∑ a, w a) : False := by
  classical
  have hsum : (∑ v : Fin n, 2 * (∑ a ∈ U v, w a)) <
      ∑ _v : Fin n, (∑ a, w a) := by
    apply sum_lt_sum (fun v _ => (hsep v).le)
    exact ⟨⟨0, hn⟩, mem_univ _, hsep _⟩
  have hcount : (∑ v : Fin n, ∑ a ∈ U v, w a) =
      ∑ a : Fin m, ((univ.filter fun v => a ∈ U v).card : ℝ) * w a := by
    calc
      (∑ v : Fin n, ∑ a ∈ U v, w a) =
          ∑ v : Fin n, ∑ a : Fin m, if a ∈ U v then w a else 0 := by
        apply sum_congr rfl
        intro v hv
        simp
      _ = ∑ a : Fin m, ∑ v : Fin n, if a ∈ U v then w a else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        simp [← sum_filter]
  have hle : (n : ℝ) * (∑ a, w a) ≤
      2 * (∑ a : Fin m, ((univ.filter fun v => a ∈ U v).card : ℝ) * w a) := by
    rw [mul_sum, mul_sum]
    apply sum_le_sum
    intro a ha
    have hc : (n : ℝ) ≤ 2 * ((univ.filter fun v => a ∈ U v).card : ℝ) := by
      exact_mod_cast hhalf a
    nlinarith [mul_le_mul_of_nonneg_right hc (hw a)]
  rw [← mul_sum, hcount] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact (not_lt_of_ge hle) hsum

theorem condorcet_half_cover_acyclic_half_cover_excluded_by_weights
    (m n : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hacyclic : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsep : ∀ A : Finset (Fin m),
      WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
      2 * (∑ a ∈ A, w a) < ∑ a, w a) : False :=
  condorcet_half_cover_finite_weighted_half_cover_exclusion m n hn U hhalf w hw (fun v => hsep _ (hacyclic v))

theorem condorcet_half_cover_winning_three_of_acyclic_weight_separation
    (hcert : ∀ (m : ℕ) (R : Fin m → Fin m → Prop),
      (∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) →
      ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
        ∀ A : Finset (Fin m),
          WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
          2 * (∑ a ∈ A, w a) < ∑ a, w a) :
    ∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
      ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S := by
  classical
  intro n m P hn
  by_contra h
  push_neg at h
  obtain ⟨q, R, U, hroot, hacyclic, hhalf⟩ :=
    (condorcet_failure_iff_acyclic_half_cover n hn).mp ⟨m, P, h⟩
  obtain ⟨w, hw, hsep⟩ := hcert q R hroot
  exact condorcet_half_cover_acyclic_half_cover_excluded_by_weights q n hn R U hacyclic hhalf w hw hsep


open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_finite_downclosed_half_hull_separation
    (m : ℕ) (C : Finset (Fin m) → Prop)
    (hdown : ∀ A B, B ⊆ A → C A → C B) :
    ((fun _ : Fin m => (1 / 2 : ℝ)) ∉
      convexHull ℝ ((fun A : Finset (Fin m) =>
        fun a => if a ∈ A then (1 : ℝ) else 0) '' {A | C A})) ↔
    ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A, C A → 2 * (∑ a ∈ A, w a) < ∑ a, w a := by
  classical
  let χ : Finset (Fin m) → (Fin m → ℝ) :=
    fun A a => if a ∈ A then 1 else 0
  let K : Set (Fin m → ℝ) := χ '' {A | C A}
  have hfin : K.Finite := (Set.toFinite {A | C A}).image χ
  constructor
  · intro hnot
    obtain ⟨f, u, hfu, huhalf⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ K) (hfin.isClosed_convexHull ℝ) hnot
    let w : Fin m → ℝ := fun a => f (Pi.single a 1)
    have hrepr (x : Fin m → ℝ) : f x = ∑ a, w a * x a := by
      have hx : x = ∑ a, x a • Pi.single a (1 : ℝ) := by
        ext a
        simp [Pi.single_apply]
      calc
        f x = f (∑ a, x a • Pi.single a (1 : ℝ)) := congrArg f hx
        _ = ∑ a, w a * x a := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
          exact sum_congr rfl (fun a _ => mul_comm _ _)
    have hchi (A : Finset (Fin m)) : f (χ A) = ∑ a ∈ A, w a := by
      rw [hrepr]
      simp [χ, mul_ite, sum_ite_mem]
    have hhalf : f (fun _ : Fin m => (1 / 2 : ℝ)) = (∑ a, w a) / 2 := by
      rw [hrepr, ← sum_mul]
      ring
    have hA (A : Finset (Fin m)) (hA : C A) :
        2 * (∑ a ∈ A, w a) < ∑ a, w a := by
      have h := hfu (χ A) (subset_convexHull ℝ K ⟨A, hA, rfl⟩)
      rw [hchi] at h
      rw [hhalf] at huhalf
      linarith
    refine ⟨fun a => max (w a) 0, fun a => le_max_right _ _, ?_⟩
    intro A hCA
    have hp := hA (A.filter fun a => 0 ≤ w a)
      (hdown A _ (filter_subset _ _) hCA)
    have heq : (∑ a ∈ A.filter (fun a => 0 ≤ w a), w a) =
        ∑ a ∈ A, max (w a) 0 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a ha
      by_cases h : 0 ≤ w a
      · simp [h, max_eq_left h]
      · simp [h, max_eq_right (le_of_not_ge h)]
    rw [heq] at hp
    exact hp.trans_le (sum_le_sum (fun a _ => le_max_left _ _))
  · rintro ⟨w, hw, hA⟩ hmem
    let f : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
      ∑ a, (LinearMap.proj a).smulRight (w a)
    have hfx (x : Fin m → ℝ) : f x = ∑ a, w a * x a := by
      simp [f, mul_comm]
    have hconv : Convex ℝ {x : Fin m → ℝ | 2 * f x < ∑ a, w a} := by
      exact (convex_Iio (∑ a, w a)).linear_preimage ((2 : ℝ) • f)
    have hsub : K ⊆ {x : Fin m → ℝ | 2 * f x < ∑ a, w a} := by
      rintro x ⟨A, hCA, rfl⟩
      change 2 * f (χ A) < ∑ a, w a
      simpa [hfx, χ, mul_ite, sum_ite_mem] using hA A hCA
    have hh := convexHull_min hsub hconv hmem
    change 2 * f (fun _ : Fin m => (1 / 2 : ℝ)) < ∑ a, w a at hh
    rw [hfx, ← sum_mul] at hh
    linarith

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_rational_barycentric_weights
    {ι : Type*} [Fintype ι] (m : ℕ) (p : ι → Fin m → ℚ)
    (hp : AffineIndependent ℝ (fun i a => (p i a : ℝ)))
    (w : ι → ℝ) (x : Fin m → ℚ)
    (hsum : ∑ i, w i = 1)
    (hcombo : (∑ i, w i • (fun a => (p i a : ℝ))) = fun a => (x a : ℝ)) :
    ∀ i, ∃ q : ℚ, w i = (q : ℝ) := by
  classical
  let c : ℚ →ₗ[ℚ] ℝ := Algebra.linearMap ℚ ℝ
  have hc : LinearMap.ker c = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro a b hab
    change (a : ℝ) = (b : ℝ) at hab
    exact_mod_cast hab
  obtain ⟨π, hπ⟩ := c.exists_leftInverse_of_injective hc
  have hπq (q : ℚ) : π (q : ℝ) = q := by
    have h := LinearMap.congr_fun hπ q
    simpa [c] using h
  have hπmul (q : ℚ) (z : ℝ) : π ((q : ℝ) * z) = q * π z := by
    rw [← smul_eq_mul, Rat.cast_smul_eq_qsmul, map_smul, smul_eq_mul]
  let v : ι → ℚ := fun i => π (w i)
  have hvsum : ∑ i, v i = 1 := by
    change ∑ i, π (w i) = 1
    rw [← map_sum, hsum]
    simpa using hπq 1
  have hvcombo (a : Fin m) : ∑ i, p i a * v i = x a := by
    have hcoord : (∑ i, (p i a : ℝ) * w i) = (x a : ℝ) := by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hcombo a
    have h := congrArg π hcoord
    simpa only [map_sum, hπmul, hπq] using h
  have heqsum : (∑ i, (v i : ℝ)) = ∑ i, w i := by
    rw [hsum]
    exact_mod_cast hvsum
  have heqcombo : (∑ i, (v i : ℝ) • (fun a => (p i a : ℝ))) =
      ∑ i, w i • (fun a => (p i a : ℝ)) := by
    rw [hcombo]
    ext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hcast : (∑ i, (p i a : ℝ) * (v i : ℝ)) = (x a : ℝ) := by
      exact_mod_cast hvcombo a
    simpa [mul_comm] using hcast
  have heq := hp.eq_of_sum_eq_sum (s := univ) heqsum heqcombo
  intro i
  exact ⟨v i, (heq i (mem_univ i)).symm⟩


open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_rational_convex_weights_of_real_hull
    (m : ℕ) (s : Set (Fin m → ℚ)) (x : Fin m → ℚ)
    (hx : (fun a => (x a : ℝ)) ∈ convexHull ℝ
      ((fun p : Fin m → ℚ => fun a => (p a : ℝ)) '' s)) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → Fin m → ℚ) (v : ι → ℚ),
      (∀ i, p i ∈ s) ∧ (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1) ∧
      ∑ i, v i • p i = x := by
  classical
  let φ : (Fin m → ℚ) → (Fin m → ℝ) := fun p a => (p a : ℝ)
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set (Fin m → ℝ)) ⊆ φ '' s :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hi : AffineIndependent ℝ ((↑) : t → (Fin m → ℝ)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hxt : (fun a => (x a : ℝ)) ∈ convexHull ℝ (t : Set (Fin m → ℝ)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  obtain ⟨w, hw, hws, hwx⟩ := Finset.mem_convexHull'.mp hxt
  have hchoose : ∀ z : t, ∃ p ∈ s, φ p = z.val := fun z => ht z.property
  choose p hps hp using hchoose
  have hp' : (fun z : t => fun a => (p z a : ℝ)) = ((↑) : t → (Fin m → ℝ)) := by
    funext z
    exact hp z
  let w' : t → ℝ := fun z => w z.val
  have hws' : ∑ z : t, w' z = 1 := by
    simpa only [w', Finset.sum_coe_sort] using hws
  have hwx' : (∑ z : t, w' z • (fun a => (p z a : ℝ))) =
      fun a => (x a : ℝ) := by
    change (∑ z : t, w' z • φ (p z)) = _
    simp_rw [hp]
    rw [← Finset.sum_coe_sort t (fun z => w z • z)] at hwx
    exact hwx
  have hi' : AffineIndependent ℝ (fun z : t => fun a => (p z a : ℝ)) := by
    rw [hp']
    exact hi
  choose v hv using condorcet_half_cover_rational_barycentric_weights m p hi' w' x hws' hwx'
  refine ⟨t, inferInstance, p, v, hps, ?_, ?_, ?_⟩
  · intro z
    have h : 0 ≤ w' z := hw z.val z.property
    rw [hv z] at h
    exact_mod_cast h
  · have h : (∑ z : t, (v z : ℝ)) = 1 := by simpa only [← hv] using hws'
    exact_mod_cast h
  · ext a
    apply Rat.cast_injective (α := ℝ)
    have h := congrFun hwx' a
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv] using h


open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_finite_nonnegative_rational_common_denominator
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    ∃ (D : ℕ) (d : ι → ℕ), 0 < D ∧ ∀ i, (D : ℚ) * w i = (d i : ℚ) := by
  classical
  let D := ∏ i, (w i).den
  let d : ι → ℕ := fun i => (w i).num.toNat * ∏ j ∈ univ.erase i, (w j).den
  have hD : 0 < D := prod_pos (fun i _ => (w i).pos)
  refine ⟨D, d, hD, ?_⟩
  intro i
  have hn : 0 ≤ (w i).num := Rat.num_nonneg.mpr (hw i)
  have hDeq : D = (w i).den * ∏ j ∈ univ.erase i, (w j).den :=
    (mul_prod_erase _ _ (mem_univ i)).symm
  have hfrac : (w i).num / ((w i).den : ℚ) = w i := Rat.num_div_den (w i)
  have hdne : ((w i).den : ℚ) ≠ 0 := by exact_mod_cast (w i).den_nz
  have hmul : ((w i).den : ℚ) * w i = ((w i).num : ℚ) := by
    exact (mul_comm _ _).trans ((div_eq_iff hdne).mp hfrac).symm
  dsimp only [d]
  rw [hDeq]
  push_cast
  have hnat : (((w i).num.toNat : ℕ) : ℚ) = ((w i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  rw [hnat]
  calc
    _ = (((w i).den : ℚ) * w i) * ∏ j ∈ univ.erase i, ((w j).den : ℚ) := by ring
    _ = _ := by rw [hmul]

theorem condorcet_half_cover_finite_rational_half_cover_to_integer
    {ι : Type*} [Fintype ι] (m : ℕ) (C : Finset (Fin m) → Prop)
    (A : ι → Finset (Fin m)) (hA : ∀ i, C (A i))
    (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hhalf : ∀ a, (∑ i, if a ∈ A i then w i else 0) = 1 / 2) :
    ∃ (n : ℕ) (U : Fin n → Finset (Fin m)), 0 < n ∧
      (∀ v, C (U v)) ∧ ∀ a, n = 2 * (univ.filter fun v => a ∈ U v).card := by
  classical
  obtain ⟨D, d, hD, hd⟩ := condorcet_half_cover_finite_nonnegative_rational_common_denominator w hw
  have hsumd : ∑ i, d i = D := by
    have h : (∑ i, (d i : ℚ)) = (D : ℚ) := by
      simp_rw [← hd]
      rw [← mul_sum, hsum, mul_one]
    exact_mod_cast h
  let V := Sigma fun i => Fin (d i)
  let n := Fintype.card V
  let e : V ≃ Fin n := Fintype.equivFin V
  let U : Fin n → Finset (Fin m) := fun v => A (e.symm v).1
  have hnD : n = D := by simpa [n, V, Fintype.card_sigma] using hsumd
  refine ⟨n, U, by omega, fun v => hA _, ?_⟩
  intro a
  have hcount : (univ.filter fun v => a ∈ U v).card =
      ∑ i, if a ∈ A i then d i else 0 := by
    calc
      (univ.filter fun v => a ∈ U v).card = ∑ v : Fin n, if a ∈ U v then 1 else 0 := by
        simp [← sum_filter]
      _ = ∑ v : V, if a ∈ A v.1 then 1 else 0 := by
        simpa only [U, Equiv.symm_apply_apply] using
          (Equiv.sum_comp e (fun v => if a ∈ U v then (1 : ℕ) else 0)).symm
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply sum_congr rfl
        intro i hi
        by_cases h : a ∈ A i <;> simp [h]
  rw [hcount, hnD]
  have h : (D : ℚ) = 2 * (∑ i, if a ∈ A i then (d i : ℚ) else 0) := by
    have hh : (∑ i, if a ∈ A i then (d i : ℚ) else 0) = (D : ℚ) * (1 / 2) := by
      simp_rw [← hd]
      calc
        _ = (D : ℚ) * (∑ i, if a ∈ A i then w i else 0) := by simp [mul_sum, mul_ite]
        _ = _ := by rw [hhalf]
    linarith
  exact_mod_cast h


open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_finite_half_hull_integer_cover
    (m : ℕ) (C : Finset (Fin m) → Prop)
    (hx : (fun _ : Fin m => (1 / 2 : ℝ)) ∈ convexHull ℝ
      ((fun A : Finset (Fin m) => fun a => if a ∈ A then (1 : ℝ) else 0) '' {A | C A})) :
    ∃ (n : ℕ) (U : Fin n → Finset (Fin m)), 0 < n ∧
      (∀ v, C (U v)) ∧ ∀ a, n = 2 * (univ.filter fun v => a ∈ U v).card := by
  classical
  let χ : Finset (Fin m) → Fin m → ℚ := fun A a => if a ∈ A then 1 else 0
  let s : Set (Fin m → ℚ) := χ '' {A | C A}
  have hcast : ((fun p : Fin m → ℚ => fun a => (p a : ℝ)) '' s) =
      ((fun A : Finset (Fin m) => fun a => if a ∈ A then (1 : ℝ) else 0) '' {A | C A}) := by
    dsimp only [s]
    rw [Set.image_image]
    congr 1
    funext A a
    by_cases h : a ∈ A <;> simp [χ, h]
  have hx' : (fun a : Fin m => ((1 / 2 : ℚ) : ℝ)) ∈ convexHull ℝ
      ((fun p : Fin m → ℚ => fun a => (p a : ℝ)) '' s) := by
    rw [hcast]
    simpa using hx
  obtain ⟨ι, hι, p, w, hps, hw, hsum, hcombo⟩ :=
    condorcet_half_cover_rational_convex_weights_of_real_hull m s (fun _ => 1 / 2) hx'
  letI : Fintype ι := hι
  have hchoose : ∀ i, ∃ A, C A ∧ χ A = p i := fun i => hps i
  choose A hA hp using hchoose
  have hhalf : ∀ a, (∑ i, if a ∈ A i then w i else 0) = (1 / 2 : ℚ) := by
    intro a
    have h := congrFun hcombo a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simp_rw [← hp] at h
    simpa [χ, mul_ite] using h
  exact condorcet_half_cover_finite_rational_half_cover_to_integer m C A hA w hw hsum hhalf

theorem condorcet_half_cover_finite_downclosed_half_cover_duality
    (m : ℕ) (C : Finset (Fin m) → Prop)
    (hdown : ∀ A B, B ⊆ A → C A → C B) :
    (¬ ∃ (n : ℕ) (U : Fin n → Finset (Fin m)), 0 < n ∧
      (∀ v, C (U v)) ∧ ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) ↔
    ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A, C A → 2 * (∑ a ∈ A, w a) < ∑ a, w a := by
  classical
  constructor
  · intro hnone
    apply (condorcet_half_cover_finite_downclosed_half_hull_separation m C hdown).mp
    intro hmem
    obtain ⟨n, U, hn, hU, hhalf⟩ := condorcet_half_cover_finite_half_hull_integer_cover m C hmem
    exact hnone ⟨n, U, hn, hU, fun a => (hhalf a).le⟩
  · rintro ⟨w, hw, hsep⟩ ⟨n, U, hn, hU, hhalf⟩
    exact condorcet_half_cover_finite_weighted_half_cover_exclusion m n hn U hhalf w hw
      (fun v => hsep _ (hU v))


open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_half_cover_acyclic_half_cover_duality
    (m : ℕ) (R : Fin m → Fin m → Prop) :
    (¬ ∃ (n : ℕ) (U : Fin n → Finset (Fin m)), 0 < n ∧
      (∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) ∧
      ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) ↔
    ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a := by
  classical
  apply condorcet_half_cover_finite_downclosed_half_cover_duality m
    (fun A => WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val))
  intro A B hBA hA
  let g : {a : Fin m // a ∈ B} → {a : Fin m // a ∈ A} :=
    fun a => ⟨a.val, hBA a.property⟩
  exact InvImage.wf g hA

theorem condorcet_dimension_le_three_iff_acyclic_weight_separation :
    (∀ (n m : ℕ) (P : Fin n → Equiv.Perm (Fin m)), 0 < n →
      ∃ S : Finset (Fin m), S.card ≤ 3 ∧ is_condorcet_winning_set P S) ↔
    (∀ (m : ℕ) (R : Fin m → Fin m → Prop),
      (∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) →
      ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
        ∀ A : Finset (Fin m),
          WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
          2 * (∑ a ∈ A, w a) < ∑ a, w a) := by
  constructor
  · intro hmain m R hroot
    apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
    rintro ⟨n, U, hn, hacyclic, hhalf⟩
    obtain ⟨P, hfail⟩ := condorcet_acyclic_cover_no_winning_three_of_acyclic_half_cover
      n m hn R U hroot hacyclic hhalf
    obtain ⟨S, hcard, hwin⟩ := hmain n m P hn
    exact hfail S hcard hwin
  · exact condorcet_half_cover_winning_three_of_acyclic_weight_separation
