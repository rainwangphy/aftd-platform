import AFTD.Prelude
import AFTD.Kb.Optimization.HypercubeIsDConvex
import AFTD.Kb.Optimization.HypercubeIsMajorityClosed
import AFTD.Kb.Optimization.HypercubeHasRelativeOppositePair
import AFTD.Kb.Optimization.HypercubeCoordReflectInvolutive
import AFTD.Kb.Optimization.HypercubeCoordReflectMaj
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Optimization.HypercubeNonconstantCoords
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Optimization.HypercubeRelativeOpposite
import AFTD.Kb.Optimization.HypercubeCoordReflect
import AFTD.Kb.Optimization.HypercubeReflectedJoin
import AFTD.Kb.Optimization.HypercubeReflectedMeet
import AFTD.Kb.Optimization.HypercubeMaj

/-!
# hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair

Topic: submodular   Node: f373d5547824

Provenance: formalization of a published result. Source: arXiv:2610.38287 Theorem 2

Let X : Finset (Fin n → Bool) be a nonempty finite subset of vertices of the unit hypercube. Then X is D-convex (hypercube_is_d_convex X) if and only if X is majority-closed (hypercube_is_majority_closed X) and contains a relative opposite pair (hypercube_has_relative_opposite_pair X).
-/

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_nonconstant_iff
    {n : ℕ} (X : Finset (Fin n → Bool)) (i : Fin n) :
    i ∈ hypercube_nonconstant_coords X ↔ (∃ x ∈ X, x i = true) ∧ (∃ x ∈ X, x i = false) := by
  rw [hypercube_nonconstant_coords, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, y, hy, hne⟩
    cases hx_i : x i <;> cases hy_i : y i
    · exfalso; apply hne; rw [hx_i, hy_i]
    · exact ⟨⟨y, hy, hy_i⟩, ⟨x, hx, hx_i⟩⟩
    · exact ⟨⟨x, hx, hx_i⟩, ⟨y, hy, hy_i⟩⟩
    · exfalso; apply hne; rw [hx_i, hy_i]
  · rintro ⟨⟨x, hx, hx_i⟩, ⟨y, hy, hy_i⟩⟩
    refine ⟨x, hx, y, hy, ?_⟩
    rw [hx_i, hy_i]
    decide

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_false
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → Bool)
    (h : ∃ a ∈ s, f a = false) : s.inf' hs f = false := by
  rcases h with ⟨a, ha, hfa⟩
  have : s.inf' hs f ≤ f a := Finset.inf'_le f ha
  rw [hfa] at this
  cases hres : s.inf' hs f
  · rfl
  · rw [hres] at this; revert this; decide

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_true
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → Bool)
    (h : ∀ a ∈ s, f a = true) : s.inf' hs f = true := by
  have : true ≤ s.inf' hs f := by
    rw [Finset.le_inf'_iff]
    intro a ha
    rw [h a ha]
  cases hres : s.inf' hs f
  · rw [hres] at this; revert this; decide
  · rfl

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_true
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → Bool)
    (h : ∃ a ∈ s, f a = true) : s.sup' hs f = true := by
  rcases h with ⟨a, ha, hfa⟩
  have : f a ≤ s.sup' hs f := Finset.le_sup' f ha
  rw [hfa] at this
  cases hres : s.sup' hs f
  · rw [hres] at this; revert this; decide
  · rfl

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_false
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → Bool)
    (h : ∀ a ∈ s, f a = false) : s.sup' hs f = false := by
  have : s.sup' hs f ≤ false := by
    rw [Finset.sup'_le_iff]
    intro a ha
    rw [h a ha]
  cases hres : s.sup' hs f
  · rfl
  · rw [hres] at this; revert this; decide

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_d_eq_meet
    {n : ℕ} (x y d : Fin n → Bool) :
    let T : Finset (Fin n) := Finset.filter (fun i => d i == true) Finset.univ
    hypercube_maj x y d = hypercube_reflected_meet T x y := by
  intro T
  ext i
  dsimp [hypercube_maj, hypercube_reflected_meet, hypercube_coord_reflect, T]
  by_cases h : d i = true
  · simp [h]; cases x i <;> cases y i <;> rfl
  · simp [h]

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_dopp_eq_join
    {n : ℕ} (X : Finset (Fin n → Bool)) (d : Fin n → Bool)
    (x y : Fin n → Bool) (hx : x ∈ X) (hy : y ∈ X) (hd : d ∈ X) :
    let T : Finset (Fin n) := Finset.filter (fun i => d i == true) Finset.univ
    hypercube_maj x y (hypercube_relative_opposite X d) = hypercube_reflected_join T x y := by
  intro T
  ext i
  dsimp [hypercube_maj, hypercube_reflected_join, hypercube_coord_reflect,
         hypercube_relative_opposite, T]
  by_cases hI : i ∈ hypercube_nonconstant_coords X
  · simp only [hI, ↓reduceIte]
    by_cases hd_i : d i = true
    · simp [hd_i]
    · simp [hd_i]
      cases x i <;> cases y i <;> rfl
  · have hx_eq_d : x i = d i := by
      by_contra hc
      have : i ∈ hypercube_nonconstant_coords X := by
        rw [hypercube_nonconstant_coords, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, x, hx, d, hd, hc⟩
      exact hI this
    have hy_eq_d : y i = d i := by
      by_contra hc
      have : i ∈ hypercube_nonconstant_coords X := by
        rw [hypercube_nonconstant_coords, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, y, hy, d, hd, hc⟩
      exact hI this
    simp only [hI, ↓reduceIte]
    by_cases hd_i : d i = true
    · simp [hd_i, hx_eq_d, hy_eq_d]
    · simp [hd_i, hx_eq_d, hy_eq_d]

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_eq_reflected_operations
    {n : ℕ} (T : Finset (Fin n)) (x y z : Fin n → Bool) :
    hypercube_maj x y z =
      hypercube_reflected_join T
        (hypercube_reflected_join T (hypercube_reflected_meet T x y) (hypercube_reflected_meet T y z))
        (hypercube_reflected_meet T z x) := by
  have h1 : hypercube_coord_reflect T (hypercube_maj x y z) =
    hypercube_maj (hypercube_coord_reflect T x) (hypercube_coord_reflect T y) (hypercube_coord_reflect T z) :=
    hypercube_coord_reflect_maj T x y z
  dsimp [hypercube_reflected_join, hypercube_reflected_meet]
  repeat rw [hypercube_coord_reflect_involutive]
  have h2 : hypercube_maj x y z = hypercube_coord_reflect T (hypercube_coord_reflect T (hypercube_maj x y z)) := by
    rw [hypercube_coord_reflect_involutive]
  rw [h2, h1]
  rfl

lemma hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_opp_eq
    {n : ℕ} (T : Finset (Fin n)) (X : Finset (Fin n → Bool)) (hX : X.Nonempty) :
    let Y := X.image (hypercube_coord_reflect T)
    let hY : Y.Nonempty := hX.image _
    let u_min := Y.inf' hY id
    let u_max := Y.sup' hY id
    let d := hypercube_coord_reflect T u_min
    let d_opp := hypercube_coord_reflect T u_max
    hypercube_relative_opposite X d = d_opp := by
  intro Y hY u_min u_max d d_opp
  ext i
  dsimp [hypercube_relative_opposite, d, d_opp, hypercube_coord_reflect, u_min, u_max]
  rw [Finset.inf'_apply, Finset.sup'_apply]
  dsimp [id]
  by_cases hI : i ∈ hypercube_nonconstant_coords X
  · simp only [hI, ↓reduceIte]
    rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_nonconstant_iff] at hI
    rcases hI with ⟨⟨xt, hxt, hxti⟩, ⟨xf, hxf, hxfi⟩⟩
    by_cases hiT : i ∈ T
    · simp only [hiT, ↓reduceIte]
      have h1 : ∃ y ∈ Y, y i = false := by
        refine ⟨hypercube_coord_reflect T xt, Finset.mem_image_of_mem _ hxt, ?_⟩
        dsimp [hypercube_coord_reflect]; simp [hiT, hxti]
      have h2 : ∃ y ∈ Y, y i = true := by
        refine ⟨hypercube_coord_reflect T xf, Finset.mem_image_of_mem _ hxf, ?_⟩
        dsimp [hypercube_coord_reflect]; simp [hiT, hxfi]
      rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_false Y hY (fun y => y i) h1]
      rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_true Y hY (fun y => y i) h2]
      rfl
    · simp only [hiT, ↓reduceIte]
      have h1 : ∃ y ∈ Y, y i = false := by
        refine ⟨hypercube_coord_reflect T xf, Finset.mem_image_of_mem _ hxf, ?_⟩
        dsimp [hypercube_coord_reflect]; simp [hiT, hxfi]
      have h2 : ∃ y ∈ Y, y i = true := by
        refine ⟨hypercube_coord_reflect T xt, Finset.mem_image_of_mem _ hxt, ?_⟩
        dsimp [hypercube_coord_reflect]; simp [hiT, hxti]
      rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_false Y hY (fun y => y i) h1]
      rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_true Y hY (fun y => y i) h2]
      rfl
  · simp only [hI, ↓reduceIte]
    rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_nonconstant_iff] at hI
    rcases hX with ⟨x0, hx0⟩
    cases hx0i : x0 i
    · have h_all : ∀ x ∈ X, x i = false := by
        intro x hx
        cases hxi : x i
        · rfl
        · exfalso; exact hI ⟨⟨x, hx, hxi⟩, ⟨x0, hx0, hx0i⟩⟩
      by_cases hiT : i ∈ T
      · simp only [hiT, ↓reduceIte]
        have h_all_Y : ∀ y ∈ Y, y i = true := by
          intro y hy
          rw [Finset.mem_image] at hy
          rcases hy with ⟨x, hx, rfl⟩
          dsimp [hypercube_coord_reflect]; simp [hiT, h_all x hx]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_true Y hY (fun y => y i) h_all_Y]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_true Y hY (fun y => y i) ⟨_, Finset.mem_image_of_mem _ hx0, by dsimp [hypercube_coord_reflect]; simp [hiT, h_all x0 hx0]⟩]
      · simp only [hiT, ↓reduceIte]
        have h_all_Y : ∀ y ∈ Y, y i = false := by
          intro y hy
          rw [Finset.mem_image] at hy
          rcases hy with ⟨x, hx, rfl⟩
          dsimp [hypercube_coord_reflect]; simp [hiT, h_all x hx]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_false Y hY (fun y => y i) ⟨_, Finset.mem_image_of_mem _ hx0, by dsimp [hypercube_coord_reflect]; simp [hiT, h_all x0 hx0]⟩]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_false Y hY (fun y => y i) h_all_Y]
    · have h_all : ∀ x ∈ X, x i = true := by
        intro x hx
        cases hxi : x i
        · exfalso; exact hI ⟨⟨x0, hx0, hx0i⟩, ⟨x, hx, hxi⟩⟩
        · rfl
      by_cases hiT : i ∈ T
      · simp only [hiT, ↓reduceIte]
        have h_all_Y : ∀ y ∈ Y, y i = false := by
          intro y hy
          rw [Finset.mem_image] at hy
          rcases hy with ⟨x, hx, rfl⟩
          dsimp [hypercube_coord_reflect]; simp [hiT, h_all x hx]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_false Y hY (fun y => y i) ⟨_, Finset.mem_image_of_mem _ hx0, by dsimp [hypercube_coord_reflect]; simp [hiT, h_all x0 hx0]⟩]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_false Y hY (fun y => y i) h_all_Y]
      · simp only [hiT, ↓reduceIte]
        have h_all_Y : ∀ y ∈ Y, y i = true := by
          intro y hy
          rw [Finset.mem_image] at hy
          rcases hy with ⟨x, hx, rfl⟩
          dsimp [hypercube_coord_reflect]; simp [hiT, h_all x hx]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_inf'_eq_true Y hY (fun y => y i) h_all_Y]
        rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_bool_sup'_eq_true Y hY (fun y => y i) ⟨_, Finset.mem_image_of_mem _ hx0, by dsimp [hypercube_coord_reflect]; simp [hiT, h_all x0 hx0]⟩]

/-- A nonempty subset of the unit hypercube is D-convex if and only if it is majority-closed and contains a relative opposite pair. -/
theorem hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair
    {n : ℕ} (X : Finset (Fin n → Bool)) (hX : X.Nonempty) :
    hypercube_is_d_convex X ↔
      (hypercube_is_majority_closed X ∧ hypercube_has_relative_opposite_pair X) := by
  constructor
  · intro hconv
    rcases hconv with ⟨T, hT⟩
    have h_maj : hypercube_is_majority_closed X := by
      intro x hx y hy z hz
      rw [hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_eq_reflected_operations T]
      refine (hT _ ?_ _ (hT _ hz _ hx).1).2
      refine (hT _ (hT _ hx _ hy).1 _ (hT _ hy _ hz).1).2
    have h_opp : hypercube_has_relative_opposite_pair X := by
      let Y := X.image (hypercube_coord_reflect T)
      have hY : Y.Nonempty := hX.image _
      have h_inf_closed : ∀ u ∈ (Y : Set (Fin n → Bool)), ∀ v ∈ (Y : Set (Fin n → Bool)), u ⊓ v ∈ (Y : Set (Fin n → Bool)) := by
        intro u hu v hv
        rw [Finset.mem_coe] at hu hv ⊢
        rw [Finset.mem_image] at hu hv ⊢
        rcases hu with ⟨x, hx, rfl⟩
        rcases hv with ⟨y, hy, rfl⟩
        refine ⟨hypercube_reflected_meet T x y, (hT x hx y hy).1, ?_⟩
        dsimp [hypercube_reflected_meet]
        rw [hypercube_coord_reflect_involutive]
      have h_sup_closed : ∀ u ∈ (Y : Set (Fin n → Bool)), ∀ v ∈ (Y : Set (Fin n → Bool)), u ⊔ v ∈ (Y : Set (Fin n → Bool)) := by
        intro u hu v hv
        rw [Finset.mem_coe] at hu hv ⊢
        rw [Finset.mem_image] at hu hv ⊢
        rcases hu with ⟨x, hx, rfl⟩
        rcases hv with ⟨y, hy, rfl⟩
        refine ⟨hypercube_reflected_join T x y, (hT x hx y hy).2, ?_⟩
        dsimp [hypercube_reflected_join]
        rw [hypercube_coord_reflect_involutive]
      have hu_min_mem : Y.inf' hY id ∈ Y :=
        Finset.inf'_mem (s := (Y : Set (Fin n → Bool))) h_inf_closed Y hY id (fun y hy => hy)
      have hu_max_mem : Y.sup' hY id ∈ Y :=
        Finset.sup'_mem (s := (Y : Set (Fin n → Bool))) h_sup_closed Y hY id (fun y hy => hy)
      rw [Finset.mem_image] at hu_min_mem hu_max_mem
      rcases hu_min_mem with ⟨d, hd, hd_eq⟩
      rcases hu_max_mem with ⟨d', hd', hd'_eq⟩
      refine ⟨d, hd, ?_⟩
      have hd_reflect : d = hypercube_coord_reflect T (Y.inf' hY id) := by
        rw [← hd_eq, hypercube_coord_reflect_involutive]
      have hd'_reflect : d' = hypercube_coord_reflect T (Y.sup' hY id) := by
        rw [← hd'_eq, hypercube_coord_reflect_involutive]
      have hopp := hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_opp_eq T X hX
      dsimp only at hopp
      subst d d'
      rw [hopp]
      exact hd'
    exact ⟨h_maj, h_opp⟩
  · rintro ⟨hmaj, ⟨d, hd, hdopp⟩⟩
    let T : Finset (Fin n) := Finset.filter (fun i => d i == true) Finset.univ
    refine ⟨T, fun x hx y hy => ⟨?_, ?_⟩⟩
    · rw [← hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_d_eq_meet]
      exact hmaj x hx y hy d hd
    · rw [← hypercube_d_convex_iff_majority_closed_and_has_relative_opposite_pair_aux_maj_dopp_eq_join X d x y hx hy hd]
      exact hmaj x hx y hy (hypercube_relative_opposite X d) hdopp
