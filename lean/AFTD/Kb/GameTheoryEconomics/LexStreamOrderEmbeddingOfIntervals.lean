import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# lex_stream_order_embedding_of_intervals

Topic: social_choice   Node: cc5863c7b330

Provenance: helper lemma. step towards countable_lex_stream_order_embedding_exists

Given a family of strictly separated intervals [l(a), r(a)] in (0, 1/2], the Cantor-type series Φ(u) = ∑_{k=0}^∞ (∏_{j<k} (r(u(j)) - l(u(j)))) · l(u(k)) defines a real order embedding of Lex(ℕ → A).
-/

private noncomputable def lex_stream_order_embedding_of_intervals_P
    {A : Type} (l r : A → ℝ) (u : ℕ → A) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (r (u j) - l (u j))

private noncomputable def lex_stream_order_embedding_of_intervals_sh
    {A : Type} (u : ℕ → A) (n : ℕ) : ℕ → A := fun k => u (n + k)

private noncomputable def lex_stream_order_embedding_of_intervals_Phi
    {A : Type} (l r : A → ℝ) (u : ℕ → A) : ℝ :=
  ∑' k, lex_stream_order_embedding_of_intervals_P l r u k * l (u k)

private lemma lex_stream_order_embedding_of_intervals_gap_pos
    {A : Type} {l r : A → ℝ} (h_lt : ∀ a, l a < r a) (a : A) : 0 < r a - l a := by
  linarith [h_lt a]

private lemma lex_stream_order_embedding_of_intervals_gap_nonneg
    {A : Type} {l r : A → ℝ} (h_lt : ∀ a, l a < r a) (a : A) : 0 ≤ r a - l a :=
  le_of_lt (lex_stream_order_embedding_of_intervals_gap_pos h_lt a)

private lemma lex_stream_order_embedding_of_intervals_gap_le
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (a : A) :
    r a - l a ≤ 1 / 2 := by
  linarith [h_pos a, h_le a]

private lemma lex_stream_order_embedding_of_intervals_P_zero
    {A : Type} (l r : A → ℝ) (u : ℕ → A) :
    lex_stream_order_embedding_of_intervals_P l r u 0 = 1 := by
  simp [lex_stream_order_embedding_of_intervals_P]

private lemma lex_stream_order_embedding_of_intervals_P_pos
    {A : Type} {l r : A → ℝ} (h_lt : ∀ a, l a < r a) (u : ℕ → A) (k : ℕ) :
    0 < lex_stream_order_embedding_of_intervals_P l r u k :=
  Finset.prod_pos fun j _ => lex_stream_order_embedding_of_intervals_gap_pos h_lt (u j)

private lemma lex_stream_order_embedding_of_intervals_P_nonneg
    {A : Type} {l r : A → ℝ} (h_lt : ∀ a, l a < r a) (u : ℕ → A) (k : ℕ) :
    0 ≤ lex_stream_order_embedding_of_intervals_P l r u k :=
  le_of_lt (lex_stream_order_embedding_of_intervals_P_pos h_lt u k)

private lemma lex_stream_order_embedding_of_intervals_P_le
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) (k : ℕ) :
    lex_stream_order_embedding_of_intervals_P l r u k ≤ (1 / 2 : ℝ) ^ k := by
  have h := Finset.prod_le_prod (s := Finset.range k)
    (f := fun j => r (u j) - l (u j)) (g := fun _ => (1 / 2 : ℝ))
    (fun j _ => lex_stream_order_embedding_of_intervals_gap_nonneg h_lt (u j))
    (fun j _ => lex_stream_order_embedding_of_intervals_gap_le h_pos h_le (u j))
  simpa [lex_stream_order_embedding_of_intervals_P] using h

private lemma lex_stream_order_embedding_of_intervals_term_nonneg
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (u : ℕ → A) (k : ℕ) :
    0 ≤ lex_stream_order_embedding_of_intervals_P l r u k * l (u k) :=
  mul_nonneg (lex_stream_order_embedding_of_intervals_P_nonneg h_lt u k) (le_of_lt (h_pos (u k)))

private lemma lex_stream_order_embedding_of_intervals_term_le
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) (k : ℕ) :
    lex_stream_order_embedding_of_intervals_P l r u k * l (u k) ≤ (1 / 2 : ℝ) ^ k * (1 / 2) := by
  have hl : l (u k) ≤ 1 / 2 := by linarith [h_lt (u k), h_le (u k)]
  have h := mul_le_mul (lex_stream_order_embedding_of_intervals_P_le h_pos h_lt h_le u k) hl
    (le_of_lt (h_pos (u k))) (by positivity)
  simpa using h

private lemma lex_stream_order_embedding_of_intervals_summable_geom :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 / 2)) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right (1 / 2)

private lemma lex_stream_order_embedding_of_intervals_term_summable
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) :
    Summable (fun k => lex_stream_order_embedding_of_intervals_P l r u k * l (u k)) := by
  refine Summable.of_norm_bounded (lex_stream_order_embedding_of_intervals_summable_geom) (fun k => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (lex_stream_order_embedding_of_intervals_term_nonneg h_pos h_lt u k)]
  exact lex_stream_order_embedding_of_intervals_term_le h_pos h_lt h_le u k

private lemma lex_stream_order_embedding_of_intervals_Phi_nonneg
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (u : ℕ → A) : 0 ≤ lex_stream_order_embedding_of_intervals_Phi l r u :=
  tsum_nonneg fun k => lex_stream_order_embedding_of_intervals_term_nonneg h_pos h_lt u k

private lemma lex_stream_order_embedding_of_intervals_geom_tsum :
    (∑' k : ℕ, (1 / 2 : ℝ) ^ k * (1 / 2)) = 1 := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private lemma lex_stream_order_embedding_of_intervals_Phi_le_one
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) :
    lex_stream_order_embedding_of_intervals_Phi l r u ≤ 1 := by
  have h := Summable.tsum_le_tsum
    (f := fun k => lex_stream_order_embedding_of_intervals_P l r u k * l (u k))
    (g := fun k : ℕ => (1 / 2 : ℝ) ^ k * (1 / 2))
    (fun k => lex_stream_order_embedding_of_intervals_term_le h_pos h_lt h_le u k)
    (lex_stream_order_embedding_of_intervals_term_summable h_pos h_lt h_le u)
    (lex_stream_order_embedding_of_intervals_summable_geom)
  rw [lex_stream_order_embedding_of_intervals_geom_tsum] at h
  simpa [lex_stream_order_embedding_of_intervals_Phi] using h

private lemma lex_stream_order_embedding_of_intervals_P_add
    {A : Type} (l r : A → ℝ) (u : ℕ → A) (n m : ℕ) :
    lex_stream_order_embedding_of_intervals_P l r u (n + m) =
      lex_stream_order_embedding_of_intervals_P l r u n *
        lex_stream_order_embedding_of_intervals_P l r
          (lex_stream_order_embedding_of_intervals_sh u n) m := by
  have h := Finset.prod_range_add (fun j => r (u j) - l (u j)) n m
  simpa [lex_stream_order_embedding_of_intervals_P, lex_stream_order_embedding_of_intervals_sh] using h

private lemma lex_stream_order_embedding_of_intervals_Phi_shift
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) (n : ℕ) :
    lex_stream_order_embedding_of_intervals_Phi l r u =
      (∑ k ∈ Finset.range n, lex_stream_order_embedding_of_intervals_P l r u k * l (u k)) +
        lex_stream_order_embedding_of_intervals_P l r u n *
          lex_stream_order_embedding_of_intervals_Phi l r (lex_stream_order_embedding_of_intervals_sh u n) := by
  have hsum := (lex_stream_order_embedding_of_intervals_term_summable h_pos h_lt h_le u).sum_add_tsum_nat_add n
  have hsum' : (∑ k ∈ Finset.range n, lex_stream_order_embedding_of_intervals_P l r u k * l (u k))
      + (∑' i : ℕ, lex_stream_order_embedding_of_intervals_P l r u (i + n) * l (u (i + n)))
      = (∑' k : ℕ, lex_stream_order_embedding_of_intervals_P l r u k * l (u k)) := hsum
  have htail : (∑' i : ℕ, lex_stream_order_embedding_of_intervals_P l r u (i + n) * l (u (i + n)))
      = lex_stream_order_embedding_of_intervals_P l r u n *
          (∑' k : ℕ, lex_stream_order_embedding_of_intervals_P l r
            (lex_stream_order_embedding_of_intervals_sh u n) k *
              l (lex_stream_order_embedding_of_intervals_sh u n k)) := by
    have hterm : ∀ i : ℕ, lex_stream_order_embedding_of_intervals_P l r u (i + n) * l (u (i + n))
        = lex_stream_order_embedding_of_intervals_P l r u n *
          (lex_stream_order_embedding_of_intervals_P l r
            (lex_stream_order_embedding_of_intervals_sh u n) i *
              l (lex_stream_order_embedding_of_intervals_sh u n i)) := by
      intro i
      rw [show i + n = n + i from Nat.add_comm i n, lex_stream_order_embedding_of_intervals_P_add]
      simp [lex_stream_order_embedding_of_intervals_sh, mul_assoc]
    simp_rw [hterm]
    rw [tsum_mul_left]
  show (∑' k : ℕ, lex_stream_order_embedding_of_intervals_P l r u k * l (u k)) = _
  rw [← hsum', htail]
  simp only [lex_stream_order_embedding_of_intervals_Phi]

private lemma lex_stream_order_embedding_of_intervals_Phi_ge
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) :
    l (u 0) ≤ lex_stream_order_embedding_of_intervals_Phi l r u := by
  have h := lex_stream_order_embedding_of_intervals_Phi_shift h_pos h_lt h_le u 1
  have h1 : (∑ k ∈ Finset.range 1, lex_stream_order_embedding_of_intervals_P l r u k * l (u k))
      = l (u 0) := by
    simp [lex_stream_order_embedding_of_intervals_P_zero]
  have h2 : 0 ≤ lex_stream_order_embedding_of_intervals_P l r u 1 *
      lex_stream_order_embedding_of_intervals_Phi l r (lex_stream_order_embedding_of_intervals_sh u 1) :=
    mul_nonneg (lex_stream_order_embedding_of_intervals_P_nonneg h_lt u 1)
      (lex_stream_order_embedding_of_intervals_Phi_nonneg h_pos h_lt _)
  rw [h, h1]
  linarith

private lemma lex_stream_order_embedding_of_intervals_Phi_le_r
    {A : Type} {l r : A → ℝ} (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a)
    (h_le : ∀ a, r a ≤ (1 / 2 : ℝ)) (u : ℕ → A) :
    lex_stream_order_embedding_of_intervals_Phi l r u ≤ r (u 0) := by
  have h := lex_stream_order_embedding_of_intervals_Phi_shift h_pos h_lt h_le u 1
  have h1 : (∑ k ∈ Finset.range 1, lex_stream_order_embedding_of_intervals_P l r u k * l (u k))
      = l (u 0) := by
    simp [lex_stream_order_embedding_of_intervals_P_zero]
  have hP : lex_stream_order_embedding_of_intervals_P l r u 1 = r (u 0) - l (u 0) := by
    simp [lex_stream_order_embedding_of_intervals_P]
  have hPhi := lex_stream_order_embedding_of_intervals_Phi_le_one h_pos h_lt h_le
    (lex_stream_order_embedding_of_intervals_sh u 1)
  have hPnn : 0 ≤ lex_stream_order_embedding_of_intervals_P l r u 1 :=
    lex_stream_order_embedding_of_intervals_P_nonneg h_lt u 1
  rw [h, h1, hP]
  nlinarith [hPhi, hPnn]

private lemma lex_stream_order_embedding_of_intervals_strictMono_lex
    {A : Type} [LinearOrder A] {l r : A → ℝ} (h_pos : ∀ a, 0 < l a)
    (h_lt : ∀ a, l a < r a) (h_le : ∀ a, r a ≤ (1 / 2 : ℝ))
    (h_sep : ∀ a b, a < b → r a < l b) {u v : ℕ → A}
    (h : Pi.Lex (· < ·) (· < ·) u v) :
    lex_stream_order_embedding_of_intervals_Phi l r u <
      lex_stream_order_embedding_of_intervals_Phi l r v := by
  obtain ⟨n, hpre, hlt⟩ := h
  have hP : lex_stream_order_embedding_of_intervals_P l r u n =
      lex_stream_order_embedding_of_intervals_P l r v n := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hpre j hj]
  have hsum : (∑ k ∈ Finset.range n, lex_stream_order_embedding_of_intervals_P l r u k * l (u k))
      = (∑ k ∈ Finset.range n, lex_stream_order_embedding_of_intervals_P l r v k * l (v k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hPk : lex_stream_order_embedding_of_intervals_P l r u k =
        lex_stream_order_embedding_of_intervals_P l r v k := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hpre j (lt_trans hj hk)]
    rw [hPk, hpre k hk]
  have h1 : l (v n) ≤ lex_stream_order_embedding_of_intervals_Phi l r
      (lex_stream_order_embedding_of_intervals_sh v n) := by
    have := lex_stream_order_embedding_of_intervals_Phi_ge h_pos h_lt h_le
      (lex_stream_order_embedding_of_intervals_sh v n)
    simpa [lex_stream_order_embedding_of_intervals_sh] using this
  have h2 : lex_stream_order_embedding_of_intervals_Phi l r
      (lex_stream_order_embedding_of_intervals_sh u n) ≤ r (u n) := by
    have := lex_stream_order_embedding_of_intervals_Phi_le_r h_pos h_lt h_le
      (lex_stream_order_embedding_of_intervals_sh u n)
    simpa [lex_stream_order_embedding_of_intervals_sh] using this
  have hlt2 : lex_stream_order_embedding_of_intervals_Phi l r
        (lex_stream_order_embedding_of_intervals_sh u n) <
      lex_stream_order_embedding_of_intervals_Phi l r
        (lex_stream_order_embedding_of_intervals_sh v n) :=
    lt_of_le_of_lt h2 (lt_of_lt_of_le (h_sep _ _ hlt) h1)
  have hu := lex_stream_order_embedding_of_intervals_Phi_shift h_pos h_lt h_le u n
  have hv := lex_stream_order_embedding_of_intervals_Phi_shift h_pos h_lt h_le v n
  rw [hu, hv, hP, hsum]
  have hpos : 0 < lex_stream_order_embedding_of_intervals_P l r v n :=
    lex_stream_order_embedding_of_intervals_P_pos h_lt v n
  nlinarith [mul_lt_mul_of_pos_left hlt2 hpos]

/-- A family of strictly separated intervals in (0, 1/2] induces an order embedding from lexicographic streams to the real line. -/
theorem lex_stream_order_embedding_of_intervals
    {A : Type} [LinearOrder A] (l r : A → ℝ)
    (h_pos : ∀ a, 0 < l a) (h_lt : ∀ a, l a < r a) (h_le : ∀ a, r a ≤ (1 / 2 : ℝ))
    (h_sep : ∀ a b, a < b → r a < l b) :
    ∃ Φ : Lex (ℕ → A) → ℝ, ∀ u v : Lex (ℕ → A), u ≤ v ↔ Φ u ≤ Φ v := by
  refine ⟨fun u => lex_stream_order_embedding_of_intervals_Phi l r (ofLex u), ?_⟩
  have key : ∀ u v : Lex (ℕ → A), u < v →
      lex_stream_order_embedding_of_intervals_Phi l r (ofLex u) <
        lex_stream_order_embedding_of_intervals_Phi l r (ofLex v) := by
    intro u v h
    exact lex_stream_order_embedding_of_intervals_strictMono_lex h_pos h_lt h_le h_sep h
  intro u v
  constructor
  · intro h
    rcases le_iff_lt_or_eq.mp h with h' | h'
    · exact le_of_lt (key u v h')
    · exact le_of_eq (congrArg (fun w : Lex (ℕ → A) =>
        lex_stream_order_embedding_of_intervals_Phi l r (ofLex w)) h')
  · intro h
    by_contra hc
    have hvu : v < u := not_le.mp hc
    have keyvu := key v u hvu
    linarith
