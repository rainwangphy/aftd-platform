import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan

/-!
# multi_label_span_ge_of_radio_labeling_top

Topic: graphs   Node: 9da74376061e

Provenance: helper lemma. arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Proposition 2.3, lower bound

Lower bound: every (m,k)-radio labeling of the complete graph K_n has span at least k(mn - 1).
-/

lemma multi_label_span_ge_of_radio_labeling_top_le_span {V : Type*} [Fintype V] (f : V → Finset ℕ)
    (x y : V) (a : ℕ) (ha : a ∈ f x) (b : ℕ) (hb : b ∈ f y) :
    b - a ≤ multi_label_span f := by
  have h1 : b - a ≤ (f y).sup (fun b' => b' - a) :=
    Finset.le_sup (f := fun b' => b' - a) hb
  have h2 : (f y).sup (fun b' => b' - a) ≤ (f x).sup (fun a' => (f y).sup (fun b' => b' - a')) :=
    Finset.le_sup (f := fun a' => (f y).sup (fun b' => b' - a')) ha
  have h3 : (f x).sup (fun a' => (f y).sup (fun b' => b' - a')) ≤
      Finset.univ.sup (fun y' => (f x).sup (fun a' => (f y').sup (fun b' => b' - a'))) :=
    Finset.le_sup (f := fun y' => (f x).sup (fun a' => (f y').sup (fun b' => b' - a'))) (Finset.mem_univ y)
  have h4 : Finset.univ.sup (fun y' => (f x).sup (fun a' => (f y').sup (fun b' => b' - a'))) ≤
      multi_label_span f :=
    Finset.le_sup (f := fun x' => Finset.univ.sup (fun y' => (f x').sup (fun a' => (f y').sup (fun b' => b' - a')))) (Finset.mem_univ x)
  exact h1.trans (h2.trans (h3.trans h4))

lemma multi_label_span_ge_of_radio_labeling_top_dist_le_one (n : ℕ) (x y : Fin n) :
    (⊤ : SimpleGraph (Fin n)).dist x y ≤ 1 := by
  by_cases h : x = y
  · subst h; rw [SimpleGraph.dist_self]; exact zero_le_one
  · rw [SimpleGraph.dist_top_of_ne h]

lemma multi_label_span_ge_of_radio_labeling_top_injOn (n m k : ℕ) (f : Fin n → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k f)
    (hk : 1 ≤ k) :
    Set.InjOn (fun (p : (Σ _ : Fin n, ℕ)) => p.2) (↑(Finset.univ.sigma f)) := by
  intro p1 hp1 p2 hp2 h_eq
  obtain ⟨x, a⟩ := p1
  obtain ⟨y, b⟩ := p2
  dsimp at h_eq
  subst h_eq
  rw [Finset.mem_coe, Finset.mem_sigma] at hp1 hp2
  by_contra h_ne
  have h_ne' : (x, a) ≠ (y, a) := by
    intro h_c
    apply h_ne
    exact Sigma.ext (Prod.ext_iff.mp h_c).1 (heq_of_eq (Prod.ext_iff.mp h_c).2)
  have h_dist := hf.2 x y a hp1.2 a hp2.2 h_ne'
  simp only [sub_self, abs_zero] at h_dist
  have h_dist_le := multi_label_span_ge_of_radio_labeling_top_dist_le_one n x y
  omega

lemma multi_label_span_ge_of_radio_labeling_top_diff_ge (n m k : ℕ) (f : Fin n → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k f)
    {x y : Fin n} {a b : ℕ} (ha : a ∈ f x) (hb : b ∈ f y) (hab : a < b) :
    a + k ≤ b := by
  have h_ne : (x, a) ≠ (y, b) := by
    intro h_c
    have : a = b := (Prod.ext_iff.mp h_c).2
    omega
  have h_dist := hf.2 x y a ha b hb h_ne
  have h_top := multi_label_span_ge_of_radio_labeling_top_dist_le_one n x y
  have h_abs : |(a : ℤ) - b| = (b : ℤ) - a := by
    rw [abs_sub_comm, abs_of_nonneg]
    omega
  rw [h_abs] at h_dist
  omega

theorem multi_label_span_ge_of_radio_labeling_top (n m k : ℕ) (f : Fin n → Finset ℕ)
    (hf : simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k f) :
    k * (m * n - 1) ≤ multi_label_span f := by
  by_cases hk : k = 0
  · subst hk; simp
  by_cases hmn : m * n = 0
  · simp [hmn]
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  have hk_ge : 1 ≤ k := hk_pos
  set pairs := Finset.univ.sigma f
  set A := pairs.image (fun p => p.2)
  have h_card_pairs : pairs.card = m * n := by
    rw [Finset.card_sigma]
    simp [hf.1, mul_comm]
  have h_inj_pairs := multi_label_span_ge_of_radio_labeling_top_injOn n m k f hf hk_ge
  have h_card_A : A.card = m * n := by
    rw [Finset.card_image_of_injOn h_inj_pairs, h_card_pairs]
  have hA_nonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  set a_min := A.min' hA_nonempty
  set a_max := A.max' hA_nonempty
  have ha_min_mem : a_min ∈ A := Finset.min'_mem A hA_nonempty
  have ha_max_mem : a_max ∈ A := Finset.max'_mem A hA_nonempty
  obtain ⟨p_min, hp_min, hp_min_eq⟩ := Finset.mem_image.mp ha_min_mem
  obtain ⟨p_max, hp_max, hp_max_eq⟩ := Finset.mem_image.mp ha_max_mem
  rw [Finset.mem_sigma] at hp_min hp_max
  have h_span_ge : a_max - a_min ≤ multi_label_span f := by
    rw [← hp_min_eq, ← hp_max_eq]
    exact multi_label_span_ge_of_radio_labeling_top_le_span f p_min.1 p_max.1 p_min.2 hp_min.2 p_max.2 hp_max.2
  have h_diff : ∀ a ∈ A, ∀ b ∈ A, a < b → a + k ≤ b := by
    intro a ha b hb hab
    obtain ⟨pa, hpa, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨pb, hpb, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_sigma] at hpa hpb
    exact multi_label_span_ge_of_radio_labeling_top_diff_ge n m k f hf hpa.2 hpb.2 hab
  have h_min : ∀ a ∈ A, a_min ≤ a := fun a ha => Finset.min'_le A a ha
  have h_max : ∀ a ∈ A, a ≤ a_max := fun a ha => Finset.le_max' A a ha
  have h_inj_g : Set.InjOn (fun a => (a - a_min) / k) (↑A) := by
    intro a ha b hb hab
    dsimp at hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have h_step : a + k ≤ b := h_diff a ha b hb hlt
      have h_le : (a - a_min) + k ≤ b - a_min := by
        have := h_min a ha; omega
      have : (a - a_min) / k < (b - a_min) / k := by
        have : (a - a_min) / k + 1 ≤ (b - a_min) / k := by
          rw [← Nat.add_div_right (a - a_min) hk_pos]
          exact Nat.div_le_div_right h_le
        omega
      omega
    · exact heq
    · have h_step : b + k ≤ a := h_diff b hb a ha hgt
      have h_le : (b - a_min) + k ≤ a - a_min := by
        have := h_min b hb; omega
      have : (b - a_min) / k < (a - a_min) / k := by
        have : (b - a_min) / k + 1 ≤ (a - a_min) / k := by
          rw [← Nat.add_div_right (b - a_min) hk_pos]
          exact Nat.div_le_div_right h_le
        omega
      omega
  generalize hd : (a_max - a_min) / k = d
  have h_sub : A.image (fun a => (a - a_min) / k) ⊆ Finset.range (d + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have : (a - a_min) / k ≤ d := by
      rw [← hd]
      exact Nat.div_le_div_right (Nat.sub_le_sub_right (h_max a ha) a_min)
    omega
  have h_card_le := Finset.card_le_card h_sub
  rw [Finset.card_image_of_injOn h_inj_g, h_card_A, Finset.card_range] at h_card_le
  have h_mn : m * n - 1 ≤ d := by omega
  have h_mul : k * (m * n - 1) ≤ k * d :=
    Nat.mul_le_mul_left k h_mn
  have h_div_mul : k * d ≤ a_max - a_min := by
    rw [← hd, mul_comm]
    exact Nat.div_mul_le_self (a_max - a_min) k
  exact (h_mul.trans h_div_mul).trans h_span_ge
