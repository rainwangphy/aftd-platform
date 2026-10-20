import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.MultiLabelSpanGeOfRadioLabelingTop
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# exists_radio_labeling_top_span_eq

Topic: graphs   Node: 135bfc70cc36

Provenance: helper lemma. arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Proposition 2.3, construction

Upper bound: the labeling f(v_i) = {ik, (n+i)k, ..., ((m-1)n+i)k} is an (m,k)-radio labeling of K_n of span k(mn - 1).
-/

open SimpleGraph

def exists_radio_labeling_top_span_eq_f (n m k : ℕ) (v : Fin n) : Finset ℕ :=
  (Finset.range m).image (fun a => (a * n + (v : ℕ)) * k)

lemma exists_radio_labeling_top_span_eq_card (n m k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (v : Fin n) :
    (exists_radio_labeling_top_span_eq_f n m k v).card = m := by
  dsimp [exists_radio_labeling_top_span_eq_f]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range m
  · intro a b hab
    have h1 : a * n + (v : ℕ) = b * n + (v : ℕ) := Nat.eq_of_mul_eq_mul_right (by omega) hab
    have h2 : a * n = b * n := Nat.add_right_cancel h1
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2

lemma exists_radio_labeling_top_span_eq_separation (n m k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∀ (x y : Fin n), ∀ a ∈ exists_radio_labeling_top_span_eq_f n m k x,
      ∀ b ∈ exists_radio_labeling_top_span_eq_f n m k y,
      (x, a) ≠ (y, b) → (k : ℤ) + 1 - ((⊤ : SimpleGraph (Fin n)).dist x y : ℤ) ≤ |(a : ℤ) - (b : ℤ)| := by
  intro x y a ha b hb hne
  rw [exists_radio_labeling_top_span_eq_f, Finset.mem_image] at ha hb
  obtain ⟨ia, hia, rfl⟩ := ha
  obtain ⟨ib, hib, rfl⟩ := hb
  by_cases hxy : x = y
  · subst hxy
    rw [dist_self, Nat.cast_zero, sub_zero]
    have hab : ia ≠ ib := by
      rintro rfl
      exact hne rfl
    have h_eq : (↑((ia * n + (x : ℕ)) * k) : ℤ) - ↑((ib * n + (x : ℕ)) * k) =
        ((ia : ℤ) - (ib : ℤ)) * (n : ℤ) * (k : ℤ) := by push_cast; ring
    rw [h_eq, abs_mul, abs_mul]
    have h_n : |(n : ℤ)| = (n : ℤ) := abs_of_nonneg (by omega)
    have h_k : |(k : ℤ)| = (k : ℤ) := abs_of_nonneg (by omega)
    rw [h_n, h_k]
    have h_diff : 1 ≤ |(ia : ℤ) - (ib : ℤ)| := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have : (ia : ℤ) - (ib : ℤ) < 0 := by omega
        rw [abs_of_neg this]; omega
      · have : 0 < (ia : ℤ) - (ib : ℤ) := by omega
        rw [abs_of_pos this]; omega
    have hn' : 2 ≤ (n : ℤ) := by omega
    have hk' : 1 ≤ (k : ℤ) := by omega
    have h1 : 2 ≤ |(ia : ℤ) - (ib : ℤ)| * (n : ℤ) := by nlinarith
    have h2 : 2 * (k : ℤ) ≤ (|(ia : ℤ) - (ib : ℤ)| * (n : ℤ)) * (k : ℤ) := by nlinarith
    linarith
  · rw [dist_top_of_ne hxy, Nat.cast_one, add_sub_cancel_right]
    have h_ne : ia * n + (x : ℕ) ≠ ib * n + (y : ℕ) := by
      intro h
      have h_mod : (ia * n + (x : ℕ)) % n = (ib * n + (y : ℕ)) % n := by rw [h]
      rw [add_comm (ia * n), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.is_lt] at h_mod
      rw [add_comm (ib * n), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.is_lt] at h_mod
      exact hxy (Fin.ext h_mod)
    have h_eq : (↑((ia * n + (x : ℕ)) * k) : ℤ) - ↑((ib * n + (y : ℕ)) * k) =
        ((ia * n + (x : ℕ) : ℤ) - (ib * n + (y : ℕ) : ℤ)) * (k : ℤ) := by push_cast; ring
    rw [h_eq, abs_mul]
    have h_k : |(k : ℤ)| = (k : ℤ) := abs_of_nonneg (by omega)
    rw [h_k]
    have h_diff : 1 ≤ |(ia * n + (x : ℕ) : ℤ) - (ib * n + (y : ℕ) : ℤ)| := by
      rcases lt_or_gt_of_ne h_ne with hlt | hgt
      · have : (ia * n + (x : ℕ) : ℤ) - (ib * n + (y : ℕ) : ℤ) < 0 := by omega
        rw [abs_of_neg this]; omega
      · have : 0 < (ia * n + (x : ℕ) : ℤ) - (ib * n + (y : ℕ) : ℤ) := by omega
        rw [abs_of_pos this]; omega
    have hk' : 1 ≤ (k : ℤ) := by omega
    nlinarith

lemma exists_radio_labeling_top_span_eq_span_le (n m k : ℕ) :
    multi_label_span (exists_radio_labeling_top_span_eq_f n m k) ≤ k * (m * n - 1) := by
  dsimp [multi_label_span]
  apply Finset.sup_le
  intro x _
  apply Finset.sup_le
  intro y _
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  rw [exists_radio_labeling_top_span_eq_f, Finset.mem_image] at ha hb
  obtain ⟨ia, hia, rfl⟩ := ha
  obtain ⟨ib, hib, rfl⟩ := hb
  rw [Finset.mem_range] at hia hib
  have hy : (y : ℕ) < n := y.is_lt
  have h1 : ib * n + (y : ℕ) < m * n := by
    have : (ib + 1) * n ≤ m * n := Nat.mul_le_mul_right n hib
    calc ib * n + (y : ℕ) < ib * n + n := by omega
    _ = (ib + 1) * n := by ring
    _ ≤ m * n := this
  have h2 : ib * n + (y : ℕ) ≤ m * n - 1 := by omega
  have h3 : (ib * n + (y : ℕ)) * k ≤ (m * n - 1) * k := Nat.mul_le_mul_right k h2
  have h4 : (ib * n + (y : ℕ)) * k - (ia * n + (x : ℕ)) * k ≤ (ib * n + (y : ℕ)) * k := Nat.sub_le _ _
  have h5 : (ib * n + (y : ℕ)) * k - (ia * n + (x : ℕ)) * k ≤ (m * n - 1) * k := h4.trans h3
  rw [mul_comm (m * n - 1) k] at h5
  exact h5

theorem exists_radio_labeling_top_span_eq (n m k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∃ f : Fin n → Finset ℕ, simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k f ∧ multi_label_span f = k * (m * n - 1) := by
  use exists_radio_labeling_top_span_eq_f n m k
  have h_rl : simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k (exists_radio_labeling_top_span_eq_f n m k) := by
    constructor
    · intro v
      exact exists_radio_labeling_top_span_eq_card n m k hn hk v
    · exact exists_radio_labeling_top_span_eq_separation n m k hn hk
  refine ⟨h_rl, ?_⟩
  have h_le := exists_radio_labeling_top_span_eq_span_le n m k
  have h_ge := multi_label_span_ge_of_radio_labeling_top n m k (exists_radio_labeling_top_span_eq_f n m k) h_rl
  exact le_antisymm h_le h_ge
