import AFTD.Prelude
import AFTD.Kb.Tcs.Wheel5Vert
import AFTD.Kb.Tcs.Wheel5
import AFTD.Kb.Tcs.Wheel5F
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# wheel5_scaled_list_uncolorable

Topic: graphs   Node: 7faf03dc8d68

Provenance: formalization of a published result. Source: arXiv:2611.03236 Lemma 3.2

For all integers t ≥ 0 and b ≥ 3t + 2, there exists a list assignment L* on the 5-wheel W₅ such that |L*(x)| = b * f_W(x) + t for every vertex x, and W₅ admits no b-fold L*-coloring.
-/

open Finset

instance wheel5_scaled_list_uncolorable_decidableRel_adj : DecidableRel wheel5.Adj := by
  intro x y; cases x <;> cases y <;> dsimp [wheel5] <;> infer_instance

lemma wheel5_scaled_list_uncolorable_disjoint_Ico_omega (a b c d : ℕ) (h : b ≤ c ∨ d ≤ a) :
    Disjoint (Finset.Ico a b) (Finset.Ico c d) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_Ico] at hx hy
  omega

def wheel5_scaled_list_uncolorable_X (t b : ℕ) : Fin 5 → Finset ℕ
| 0 => Finset.Ico 0 (b - 2*t - 1)
| 1 => Finset.Ico (b - 2*t - 1) (2 * (b - 2*t - 1))
| 2 => Finset.Ico (2 * (b - 2*t - 1)) (3 * (b - 2*t - 1))
| 3 => Finset.Ico (3 * (b - 2*t - 1)) (3 * (b - 2*t - 1) + (2*b - 2*t - 1))
| 4 => Finset.Ico (3 * (b - 2*t - 1) + (2*b - 2*t - 1)) (4 * (b - 2*t - 1) + (2*b - 2*t - 1))

def wheel5_scaled_list_uncolorable_Y (t b : ℕ) : Finset ℕ :=
  Finset.Ico (4 * (b - 2*t - 1) + (2*b - 2*t - 1)) (4 * (b - 2*t - 1) + (2*b - 2*t - 1) + (5*t + 2))

def wheel5_scaled_list_uncolorable_L (t b : ℕ) : Wheel5Vert → Finset ℕ
| .u => Finset.Ico 0 (4 * b + t)
| .v i =>
  match i with
  | 0 => wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_Y t b
  | 1 => wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_X t b 1 ∪ wheel5_scaled_list_uncolorable_Y t b
  | 2 => wheel5_scaled_list_uncolorable_X t b 1 ∪ wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_Y t b
  | 3 => wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_X t b 3 ∪ wheel5_scaled_list_uncolorable_Y t b
  | 4 => wheel5_scaled_list_uncolorable_X t b 3 ∪ wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_Y t b

lemma wheel5_scaled_list_uncolorable_L_card (t b : ℕ) (hb : 3 * t + 2 ≤ b) (x : Wheel5Vert) :
    (wheel5_scaled_list_uncolorable_L t b x).card = b * wheel5_f x + t := by
  cases x with
  | u =>
    dsimp [wheel5_scaled_list_uncolorable_L, wheel5_f]
    rw [Nat.card_Ico]
    omega
  | v i =>
    fin_cases i <;> {
      dsimp [wheel5_scaled_list_uncolorable_L, wheel5_f, wheel5_scaled_list_uncolorable_X, wheel5_scaled_list_uncolorable_Y]
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
      · simp only [Nat.card_Ico]; omega
      · apply wheel5_scaled_list_uncolorable_disjoint_Ico_omega; omega
      · rw [Finset.disjoint_union_left]
        refine ⟨?_, ?_⟩
        · apply wheel5_scaled_list_uncolorable_disjoint_Ico_omega; omega
        · apply wheel5_scaled_list_uncolorable_disjoint_Ico_omega; omega
    }

def wheel5_scaled_list_uncolorable_triangle (i : Fin 5) : Finset Wheel5Vert :=
  {Wheel5Vert.u, Wheel5Vert.v i, Wheel5Vert.v ⟨(i.val + 1) % 5, by omega⟩}

lemma wheel5_scaled_list_uncolorable_triangle_indep_card_le_one (i : Fin 5) (s : Finset Wheel5Vert)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ wheel5.Adj x y)
    (h_sub : s ⊆ wheel5_scaled_list_uncolorable_triangle i) : s.card ≤ 1 := by
  have H : ∀ (i : Fin 5) (s : Finset Wheel5Vert),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ wheel5.Adj x y) →
      s ⊆ wheel5_scaled_list_uncolorable_triangle i → s.card ≤ 1 := by
    decide
  exact H i s hs h_sub

lemma wheel5_scaled_list_uncolorable_indep_card_le_two (s : Finset Wheel5Vert)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ wheel5.Adj x y) : s.card ≤ 2 := by
  have H : ∀ s : Finset Wheel5Vert,
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ wheel5.Adj x y) → s.card ≤ 2 := by
    decide
  exact H s hs

lemma wheel5_scaled_list_uncolorable_mem_L_imp_mem_triangle (t b : ℕ) (i : Fin 5) (x : Wheel5Vert) (c : ℕ)
    (hc : c ∈ wheel5_scaled_list_uncolorable_X t b i) (h : c ∈ wheel5_scaled_list_uncolorable_L t b x) :
    x ∈ wheel5_scaled_list_uncolorable_triangle i := by
  cases x with
  | u =>
    dsimp [wheel5_scaled_list_uncolorable_triangle]
    simp
  | v j =>
    revert hc h
    fin_cases i <;> fin_cases j <;> {
      dsimp [wheel5_scaled_list_uncolorable_L, wheel5_scaled_list_uncolorable_triangle, wheel5_scaled_list_uncolorable_X, wheel5_scaled_list_uncolorable_Y]
      intro hc h
      simp only [Finset.mem_union, Finset.mem_Ico] at hc h ⊢
      try { tauto }
      try { omega }
    }

lemma wheel5_scaled_list_uncolorable_union_all (t b : ℕ) :
    wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_X t b 1 ∪
    wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_X t b 3 ∪
    wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_Y t b =
    Finset.Ico 0 (4 * (b - 2*t - 1) + (2*b - 2*t - 1) + (5*t + 2)) := by
  dsimp [wheel5_scaled_list_uncolorable_X, wheel5_scaled_list_uncolorable_Y]
  rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]

lemma wheel5_scaled_list_uncolorable_L_subset_union (t b : ℕ) (hb : 3 * t + 2 ≤ b) (x : Wheel5Vert) :
    wheel5_scaled_list_uncolorable_L t b x ⊆
    wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_X t b 1 ∪
    wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_X t b 3 ∪
    wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_Y t b := by
  cases x with
  | u =>
    rw [wheel5_scaled_list_uncolorable_union_all]
    dsimp [wheel5_scaled_list_uncolorable_L]
    intro c hc
    rw [Finset.mem_Ico] at hc ⊢
    omega
  | v i =>
    fin_cases i <;> {
      dsimp [wheel5_scaled_list_uncolorable_L]
      intro c hc
      simp only [Finset.mem_union] at hc ⊢
      tauto
    }

lemma wheel5_scaled_list_uncolorable_sum_split (t b : ℕ) (g : ℕ → ℕ) :
    ∑ c ∈ (wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_X t b 1 ∪
           wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_X t b 3 ∪
           wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_Y t b), g c =
    (∑ c ∈ wheel5_scaled_list_uncolorable_X t b 0, g c) +
    (∑ c ∈ wheel5_scaled_list_uncolorable_X t b 1, g c) +
    (∑ c ∈ wheel5_scaled_list_uncolorable_X t b 2, g c) +
    (∑ c ∈ wheel5_scaled_list_uncolorable_X t b 3, g c) +
    (∑ c ∈ wheel5_scaled_list_uncolorable_X t b 4, g c) +
    (∑ c ∈ wheel5_scaled_list_uncolorable_Y t b, g c) := by
  dsimp [wheel5_scaled_list_uncolorable_X, wheel5_scaled_list_uncolorable_Y]
  rw [Finset.sum_union]
  · rw [Finset.sum_union]
    · rw [Finset.sum_union]
      · rw [Finset.sum_union]
        · rw [Finset.sum_union]
          · apply wheel5_scaled_list_uncolorable_disjoint_Ico_omega; omega
        · rw [Finset.disjoint_union_left]
          exact ⟨wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega),
                 wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩
      · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega),
                wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
               wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨⟨wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega),
               wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
              wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
             wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩
  · rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨⟨⟨wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega),
             wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
            wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
           wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩,
          wheel5_scaled_list_uncolorable_disjoint_Ico_omega _ _ _ _ (by omega)⟩

/-- Scaled list uncolorability of the 5-wheel (arXiv:2611.03236 Lemma 3.2). -/
theorem wheel5_scaled_list_uncolorable (t : ℕ) (b : ℕ) (hb : 3 * t + 2 ≤ b) :
    ∃ (L : Wheel5Vert → Finset ℕ),
      (∀ x, (L x).card = b * wheel5_f x + t) ∧
      ¬ ∃ (φ : Wheel5Vert → Finset ℕ),
        (∀ x, φ x ⊆ L x ∧ (φ x).card = b) ∧
        ∀ {x y}, wheel5.Adj x y → Disjoint (φ x) (φ y) := by
  use wheel5_scaled_list_uncolorable_L t b
  refine ⟨wheel5_scaled_list_uncolorable_L_card t b hb, ?_⟩
  rintro ⟨φ, hφ1, hφ2⟩
  let T := wheel5_scaled_list_uncolorable_X t b 0 ∪ wheel5_scaled_list_uncolorable_X t b 1 ∪
           wheel5_scaled_list_uncolorable_X t b 2 ∪ wheel5_scaled_list_uncolorable_X t b 3 ∪
           wheel5_scaled_list_uncolorable_X t b 4 ∪ wheel5_scaled_list_uncolorable_Y t b
  have hT_sub (x : Wheel5Vert) : φ x ⊆ T :=
    (hφ1 x).1.trans (wheel5_scaled_list_uncolorable_L_subset_union t b hb x)
  have h_filter (x : Wheel5Vert) : T.filter (fun c => c ∈ φ x) = φ x := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hT_sub x h, h⟩
  have h_dc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun x c => c ∈ φ x) (s := Finset.univ) (t := T)
  dsimp [Finset.bipartiteAbove, Finset.bipartiteBelow] at h_dc
  have h_lhs : ∑ x ∈ (Finset.univ : Finset Wheel5Vert), (T.filter (fun c => c ∈ φ x)).card = 6 * b := by
    simp_rw [h_filter, (hφ1 _).2]
    have hcard : (Finset.univ : Finset Wheel5Vert).card = 6 := by decide
    rw [Finset.sum_const, hcard]
    simp
  rw [h_lhs] at h_dc
  let S (c : ℕ) := Finset.univ.filter (fun x => c ∈ φ x)
  have hS_indep (c : ℕ) (x : Wheel5Vert) (hx : x ∈ S c) (y : Wheel5Vert) (hy : y ∈ S c)
      (hxy : x ≠ y) : ¬ wheel5.Adj x y := by
    rw [Finset.mem_filter] at hx hy
    intro hadj
    have hdisj := hφ2 hadj
    rw [Finset.disjoint_left] at hdisj
    exact hdisj hx.2 hy.2
  have h_card_X (i : Fin 5) (c : ℕ) (hc : c ∈ wheel5_scaled_list_uncolorable_X t b i) : (S c).card ≤ 1 := by
    apply wheel5_scaled_list_uncolorable_triangle_indep_card_le_one i (S c) (hS_indep c)
    intro x hx
    rw [Finset.mem_filter] at hx
    exact wheel5_scaled_list_uncolorable_mem_L_imp_mem_triangle t b i x c hc ((hφ1 x).1 hx.2)
  have h_card_Y (c : ℕ) (_hc : c ∈ wheel5_scaled_list_uncolorable_Y t b) : (S c).card ≤ 2 :=
    wheel5_scaled_list_uncolorable_indep_card_le_two (S c) (hS_indep c)
  have h_sum_split := wheel5_scaled_list_uncolorable_sum_split t b (fun c => (S c).card)
  have h_dc_S : ∑ b ∈ T, (S b).card = 6 * b := h_dc.symm
  rw [h_sum_split] at h_dc_S
  have h_bound_X (i : Fin 5) :
      ∑ c ∈ wheel5_scaled_list_uncolorable_X t b i, (S c).card ≤ (wheel5_scaled_list_uncolorable_X t b i).card := by
    have : ∑ c ∈ wheel5_scaled_list_uncolorable_X t b i, (S c).card ≤
           ∑ c ∈ wheel5_scaled_list_uncolorable_X t b i, 1 :=
      Finset.sum_le_sum (fun c hc => h_card_X i c hc)
    have h_const : ∑ c ∈ wheel5_scaled_list_uncolorable_X t b i, 1 =
                   (wheel5_scaled_list_uncolorable_X t b i).card :=
      (Finset.card_eq_sum_ones (wheel5_scaled_list_uncolorable_X t b i)).symm
    linarith
  have h_bound_Y :
      ∑ c ∈ wheel5_scaled_list_uncolorable_Y t b, (S c).card ≤ 2 * (wheel5_scaled_list_uncolorable_Y t b).card := by
    have : ∑ c ∈ wheel5_scaled_list_uncolorable_Y t b, (S c).card ≤
           ∑ c ∈ wheel5_scaled_list_uncolorable_Y t b, 2 :=
      Finset.sum_le_sum (fun c hc => h_card_Y c hc)
    have h_const : ∑ c ∈ wheel5_scaled_list_uncolorable_Y t b, 2 =
                   2 * (wheel5_scaled_list_uncolorable_Y t b).card := by
      have : (fun (_ : ℕ) => 2) = fun _ => 1 + 1 := rfl
      rw [this, Finset.sum_add_distrib]
      simp only [← Finset.card_eq_sum_ones]
      omega
    linarith
  have h_card_sum : (wheel5_scaled_list_uncolorable_X t b 0).card +
      (wheel5_scaled_list_uncolorable_X t b 1).card +
      (wheel5_scaled_list_uncolorable_X t b 2).card +
      (wheel5_scaled_list_uncolorable_X t b 3).card +
      (wheel5_scaled_list_uncolorable_X t b 4).card +
      2 * (wheel5_scaled_list_uncolorable_Y t b).card = 6 * b - 1 := by
    dsimp [wheel5_scaled_list_uncolorable_X, wheel5_scaled_list_uncolorable_Y]
    simp only [Nat.card_Ico]
    omega
  have h_total : 6 * b ≤ (wheel5_scaled_list_uncolorable_X t b 0).card +
      (wheel5_scaled_list_uncolorable_X t b 1).card +
      (wheel5_scaled_list_uncolorable_X t b 2).card +
      (wheel5_scaled_list_uncolorable_X t b 3).card +
      (wheel5_scaled_list_uncolorable_X t b 4).card +
      2 * (wheel5_scaled_list_uncolorable_Y t b).card := by
    linarith [h_dc_S, h_bound_X 0, h_bound_X 1, h_bound_X 2, h_bound_X 3, h_bound_X 4, h_bound_Y]
  omega
