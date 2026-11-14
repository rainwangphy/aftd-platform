import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.ChorePropShareLeMaximinShare
import AFTD.Kb.Tcs.G

/-!
# balanced_high_count_chore_mms_bound

Topic: fair_division   Node: 57697109060c

Provenance: helper lemma. Bivalued specialization of the proportional-share lower bound in arXiv:2609.35280, Lemma 2.4.

For n at least two, k at least two and n*k bivalued chores, a bundle of size k whose high-cost count times n is at most the total high-cost count plus n minus one costs at most (r+1)/2 times the n-agent chore maximin share, for every ratio r at least one and positive base cost a.
-/

lemma balanced_high_count_chore_mms_bound_sum_bivalued {α : Type*} [DecidableEq α] (s : Finset α) (u : α → ℝ) (a r : ℝ)
    (hu : ∀ g ∈ s, u g = a ∨ u g = r * a) :
    ∑ g ∈ s, u g = (s.card : ℝ) * a + ((s.filter fun g => u g = r * a).card : ℝ) * ((r - 1) * a) := by
  classical
  have hsum := (Finset.sum_filter_add_sum_filter_not s (fun g => u g = r * a) u).symm
  have hcard := (Finset.card_filter_add_card_filter_not (s := s) (fun g => u g = r * a)).symm
  have h1 : ∑ g ∈ s.filter (fun g => u g = r * a), u g = (s.filter (fun g => u g = r * a)).card * (r * a) := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)]
    simp
  have h2 : ∑ g ∈ s.filter (fun g => ¬ u g = r * a), u g = (s.filter (fun g => ¬ u g = r * a)).card * a := by
    have : ∑ g ∈ s.filter (fun g => ¬ u g = r * a), u g = ∑ g ∈ s.filter (fun g => ¬ u g = r * a), a := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' := Finset.mem_filter.mp hx
      cases hu x hx'.1 with
      | inl h => exact h
      | inr h => exact False.elim (hx'.2 h)
    rw [this]
    simp
  rw [hsum, h1, h2]
  have hcard_cast : (s.card : ℝ) = ((s.filter (fun g => u g = r * a)).card : ℝ) + ((s.filter (fun g => ¬ u g = r * a)).card : ℝ) := by
    exact_mod_cast hcard
  linear_combination
    -a * hcard_cast

theorem balanced_high_count_chore_mms_bound (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (r : ℝ) (hr : 1 ≤ r) (a : ℝ) (ha : 0 < a) (u : Fin (n*k) → ℝ) (hu : ∀ g, u g = a ∨ u g = r*a) (S : Finset (Fin (n*k))) (hs : S.card = k) (hh : n * ((S.filter fun g => u g = r*a).card) ≤ ((Finset.univ.filter fun g => u g = r*a).card) + n - 1) : additive_valuation u S ≤ ((r+1)/2) * chore_maximin_share n u := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hprop := chore_prop_share_le_maximin_share n (n * k) u
  have hS_sum : ∑ g ∈ S, u g = (k : ℝ) * a + ((S.filter fun g => u g = r * a).card : ℝ) * ((r - 1) * a) := by
    have := balanced_high_count_chore_mms_bound_sum_bivalued S u a r (fun g _ => hu g)
    rw [hs] at this
    exact this
  have huniv_sum : ∑ g : Fin (n * k), u g = ((n * k : ℕ) : ℝ) * a + ((Finset.univ.filter fun g => u g = r * a).card : ℝ) * ((r - 1) * a) := by
    have := balanced_high_count_chore_mms_bound_sum_bivalued (Finset.univ : Finset (Fin (n * k))) u a r (fun g _ => hu g)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this
  change ∑ g ∈ S, u g ≤ ((r + 1) / 2) * chore_maximin_share n u
  rw [hS_sum]
  set hS := ((S.filter fun g => u g = r * a).card : ℝ)
  set hU := ((Finset.univ.filter fun g => u g = r * a).card : ℝ)
  set P := (∑ g : Fin (n * k), u g) / (n : ℝ)
  have hP_eq : P = (k : ℝ) * a + (hU / (n : ℝ)) * ((r - 1) * a) := by
    dsimp [P]
    rw [huniv_sum]
    push_cast
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hh_real : (n : ℝ) * hS ≤ hU + (n : ℝ) - 1 := by
    have h2 : n * (S.filter fun g => u g = r * a).card + 1 ≤ (Finset.univ.filter fun g => u g = r * a).card + n := by omega
    have h3 : ((n * (S.filter fun g => u g = r * a).card + 1 : ℕ) : ℝ) ≤ (((Finset.univ.filter fun g => u g = r * a).card + n : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hr_sub : 0 ≤ r - 1 := by linarith
  have ha_nonneg : 0 ≤ a := by linarith
  have h_da : 0 ≤ (r - 1) * a := mul_nonneg hr_sub ha_nonneg
  have hk_cast : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hP_ge : 2 * a ≤ P := by
    have h1 : (k : ℝ) * a ≤ P := by
      rw [hP_eq]
      have : 0 ≤ (hU / (n : ℝ)) * ((r - 1) * a) := by positivity
      linarith
    have h2 : 2 * a ≤ (k : ℝ) * a := by nlinarith
    linarith
  have h_step1 : (k : ℝ) * a + hS * ((r - 1) * a) ≤ P + (r - 1) * a := by
    have hdiff : (P + (r - 1) * a) - ((k : ℝ) * a + hS * ((r - 1) * a)) =
        ((r - 1) * a) * ((hU + (n : ℝ) - (n : ℝ) * hS) / (n : ℝ)) := by
      rw [hP_eq]
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [sub_nonneg.symm, hdiff]
    apply mul_nonneg h_da
    apply div_nonneg _ (by positivity)
    linarith
  have h_step2 : P + (r - 1) * a ≤ ((r + 1) / 2) * P := by
    have hdiff : ((r + 1) / 2) * P - (P + (r - 1) * a) = ((r - 1) / 2) * (P - 2 * a) := by
      ring
    rw [sub_nonneg.symm, hdiff]
    exact mul_nonneg (by linarith) (by linarith)
  have h_le_P : (k : ℝ) * a + hS * ((r - 1) * a) ≤ ((r + 1) / 2) * P := le_trans h_step1 h_step2
  have hr1 : 0 ≤ (r + 1) / 2 := by linarith
  have h_final : ((r + 1) / 2) * P ≤ ((r + 1) / 2) * chore_maximin_share n u :=
    mul_le_mul_of_nonneg_left hprop hr1
  exact le_trans h_le_P h_final
