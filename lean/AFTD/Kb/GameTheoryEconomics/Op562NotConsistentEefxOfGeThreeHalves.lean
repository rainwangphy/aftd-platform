import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasConsistentEefxAlgorithm
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxBundle
import AFTD.Kb.GameTheoryEconomics.IsConsistentAlgorithm
import AFTD.Kb.GameTheoryEconomics.SortedTuple
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm
import AFTD.Kb.GameTheoryEconomics.IsAlphaEefxAllocation
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsOverestimatePrediction
import AFTD.Kb.GameTheoryEconomics.GuaranteesAlphaEefx
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# op562_not_consistent_eefx_of_ge_three_halves

Topic: fair_division   Node: 8abf9e156681

Provenance: formalization of a published result. Source: arXiv:2610.34625 Section G.6

For any number of agents n at least 3 and any error factor rho at least 3/2, no consistent online algorithm can guarantee any positive approximation of EEFX.
-/

/-- The predicted (and exact) common value profile: `h` goods of values `(2/3)^(t+1)`,
then `n - 3` goods of value `3`, then a last good of value `1`. -/
noncomputable def op562nc_W (h n : ℕ) : Fin (h + n - 2) → ℝ := fun t =>
  if t.val < h then (2 / 3 : ℝ) ^ (t.val + 1) else if t.val < h + n - 3 then 3 else 1

/-- The true profile: as `op562nc_W`, but the last good is worth `(2/3)^(h+1)`. -/
noncomputable def op562nc_V (h n : ℕ) : Fin (h + n - 2) → ℝ := fun t =>
  if t.val < h then (2 / 3 : ℝ) ^ (t.val + 1) else if t.val < h + n - 3 then 3
  else (2 / 3 : ℝ) ^ (h + 1)

theorem op562nc_sorted_eq {m : ℕ} (f : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hmono : Monotone (f ∘ σ)) : sorted_tuple f = f ∘ σ := by
  unfold sorted_tuple
  exact ((Tuple.comp_sort_eq_comp_iff_monotone).mpr hmono).symm

theorem op562nc_sorted_W (h n : ℕ) (hn : 3 ≤ n) :
    ∀ r : Fin (h + n - 2), sorted_tuple (op562nc_W h n) r =
      if r.val ≤ h then (2 / 3 : ℝ) ^ (h - r.val) else 3 := by
  let f : Fin (h + n - 2) → Fin (h + n - 2) := fun r =>
    if hr : r.val < h then ⟨h - 1 - r.val, by omega⟩
    else if r.val = h then ⟨h + n - 3, by omega⟩ else ⟨r.val - 1, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    apply Fin.ext
    split_ifs at hab <;> simp only [Fin.mk.injEq] at hab <;> omega
  let σ : Equiv.Perm (Fin (h + n - 2)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hfv : ∀ r, (σ r).val = if r.val < h then h - 1 - r.val
      else if r.val = h then h + n - 3 else r.val - 1 := by
    intro r
    simp only [σ, Equiv.ofBijective_apply, f]
    split_ifs <;> rfl
  have hval : ∀ r, op562nc_W h n (σ r) = if r.val ≤ h then (2 / 3 : ℝ) ^ (h - r.val) else 3 := by
    intro r
    unfold op562nc_W
    rw [hfv r]
    split_ifs <;> first | omega | rfl | (rw [show h - r.val = 0 by omega, pow_zero]) | (congr 1; omega)
  have hmono : Monotone (op562nc_W h n ∘ σ) := by
    intro a b hab
    simp only [Function.comp, hval]
    have hab' : a.val ≤ b.val := hab
    split_ifs with h1 h2 h2
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact le_trans (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    · omega
    · exact le_refl _
  intro r
  rw [op562nc_sorted_eq _ σ hmono]
  exact hval r

theorem op562nc_sorted_V (h n : ℕ) (hn : 3 ≤ n) :
    ∀ r : Fin (h + n - 2), sorted_tuple (op562nc_V h n) r =
      if r.val ≤ h then (2 / 3 : ℝ) ^ (h + 1 - r.val) else 3 := by
  let f : Fin (h + n - 2) → Fin (h + n - 2) := fun r =>
    if r.val = 0 then ⟨h + n - 3, by omega⟩
    else if hr : r.val ≤ h then ⟨h - r.val, by omega⟩ else ⟨r.val - 1, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    apply Fin.ext
    split_ifs at hab <;> simp only [Fin.mk.injEq] at hab <;> omega
  let σ : Equiv.Perm (Fin (h + n - 2)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hfv : ∀ r, (σ r).val = if r.val = 0 then h + n - 3
      else if r.val ≤ h then h - r.val else r.val - 1 := by
    intro r
    simp only [σ, Equiv.ofBijective_apply, f]
    split_ifs <;> rfl
  have hval : ∀ r, op562nc_V h n (σ r) =
      if r.val ≤ h then (2 / 3 : ℝ) ^ (h + 1 - r.val) else 3 := by
    intro r
    unfold op562nc_V
    rw [hfv r]
    split_ifs <;> first | omega | rfl | (congr 1; omega)
  have hmono : Monotone (op562nc_V h n ∘ σ) := by
    intro a b hab
    simp only [Function.comp, hval]
    have hab' : a.val ≤ b.val := hab
    split_ifs with h1 h2 h2
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact le_trans (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
    · omega
    · exact le_refl _
  intro r
  rw [op562nc_sorted_eq _ σ hmono]
  exact hval r

theorem op562nc_overestimate (h n : ℕ) (hn : 3 ≤ n) (ρ : ℝ) (hρ : 3 / 2 ≤ ρ) :
    is_overestimate_prediction ρ (fun _ : Fin n => op562nc_V h n)
      (fun _ : Fin n => op562nc_W h n) := by
  intro i r
  simp only
  rw [op562nc_sorted_W h n hn r, op562nc_sorted_V h n hn r]
  split_ifs with hr
  · have he : h + 1 - r.val = (h - r.val) + 1 := by omega
    rw [he, pow_succ]
    have hp : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ (h - r.val) := by positivity
    constructor
    · nlinarith
    · nlinarith
  · constructor
    · exact le_refl _
    · nlinarith

/-- Pigeonhole for EEFX partitions: `n` distinct goods outside the bundle, two share a part. -/
theorem op562nc_pigeon {m n : ℕ} (hn : 3 ≤ n) (Y : Fin (n - 1) → Finset (Fin m))
    (S : Finset (Fin m)) (hY : Finset.biUnion Finset.univ Y = Finset.univ \ S)
    (e : Fin n → Fin m) (he : Function.Injective e) (hS : ∀ j, e j ∉ S) :
    ∃ p, ∃ j1 j2, j1 ≠ j2 ∧ e j1 ∈ Y p ∧ e j2 ∈ Y p := by
  classical
  have hcov : ∀ x, x ∉ S → ∃ p, x ∈ Y p := by
    intro x hx
    have : x ∈ Finset.biUnion Finset.univ Y := by
      rw [hY]; simp [hx]
    simpa using this
  let part : Fin m → Fin (n - 1) := fun x =>
    if hx : ∃ p, x ∈ Y p then Classical.choose hx else ⟨0, by omega⟩
  have hpart : ∀ x, x ∉ S → x ∈ Y (part x) := by
    intro x hx
    simp only [part, dif_pos (hcov x hx)]
    exact Classical.choose_spec (hcov x hx)
  obtain ⟨j1, j2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (part ∘ e)
    (by simp; omega)
  refine ⟨part (e j1), j1, j2, hne, hpart _ (hS j1), ?_⟩
  have := hpart _ (hS j2)
  simp only [Function.comp] at heq
  rwa [heq]

theorem op562nc_av_mono {m : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g) {A B : Finset (Fin m)}
    (hAB : A ⊆ B) : additive_valuation u A ≤ additive_valuation u B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun _ _ _ => hu _)

/-- Two distinct goods in one part: erasing one leaves at least the other's value. -/
theorem op562nc_two_in_part {m : ℕ} (u : Fin m → ℝ) (hu : ∀ g, 0 ≤ u g) (P : Finset (Fin m))
    {a b : Fin m} (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) :
    u b ≤ additive_valuation u (P.erase a) := by
  have : ({b} : Finset (Fin m)) ⊆ P.erase a := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩
  have := op562nc_av_mono u hu this
  simpa [additive_valuation] using this

theorem op562nc_V_nonneg (h n : ℕ) : ∀ g, 0 ≤ op562nc_V h n g := by
  intro g; unfold op562nc_V; split_ifs <;> positivity

theorem op562nc_W_nonneg (h n : ℕ) : ∀ g, 0 ≤ op562nc_W h n g := by
  intro g; unfold op562nc_W; split_ifs <;> positivity

/-- The inexact instance: an agent whose bundle is inside the last good is not α-EEFX. -/
theorem op562nc_fail (h n : ℕ) (hn : 3 ≤ n) (hh : 3 ≤ h) (α : ℝ)
    (hα : (2 / 3 : ℝ) ^ (h + 1) < α * (2 / 3) ^ 3) (S : Finset (Fin (h + n - 2)))
    (hS : ∀ t ∈ S, t.val = h + n - 3) :
    ¬ is_alpha_eefx_bundle (additive_valuation (op562nc_V h n)) n α S := by
  rintro ⟨Y, _hdisj, hY, hefx⟩
  let e : Fin n → Fin (h + n - 2) := fun j =>
    if j.val < 3 then ⟨j.val, by omega⟩ else ⟨h + j.val - 3, by omega⟩
  have he : Function.Injective e := by
    intro a b hab
    simp only [e] at hab
    apply Fin.ext
    split_ifs at hab <;> simp only [Fin.mk.injEq] at hab <;> omega
  have heS : ∀ j, e j ∉ S := by
    intro j hj
    have := hS _ hj
    simp only [e] at this
    split_ifs at this <;> simp only at this <;> omega
  have hev : ∀ j, (2 / 3 : ℝ) ^ 3 ≤ op562nc_V h n (e j) := by
    intro j
    simp only [e, op562nc_V]
    split_ifs with h1 h2 h3 h4 h5 <;> simp only at * <;> try omega
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · norm_num
  obtain ⟨p, j1, j2, hne, h1, h2⟩ := op562nc_pigeon hn Y S hY e he heS
  have hle := hefx p (e j1) h1
  have hbig := op562nc_two_in_part (op562nc_V h n) (op562nc_V_nonneg h n) (Y p)
    (fun h => hne (he h)) h1 h2
  have hSv : additive_valuation (op562nc_V h n) S ≤ (2 / 3 : ℝ) ^ (h + 1) := by
    have hsub : S ⊆ {(⟨h + n - 3, by omega⟩ : Fin (h + n - 2))} := by
      intro t ht
      rw [Finset.mem_singleton]
      exact Fin.ext (hS t ht)
    have := op562nc_av_mono (op562nc_V h n) (op562nc_V_nonneg h n) hsub
    refine le_trans this (le_of_eq ?_)
    unfold additive_valuation
    rw [Finset.sum_singleton]
    unfold op562nc_V
    show (if h + n - 3 < h then _ else if h + n - 3 < h + n - 3 then (3 : ℝ)
      else (2 / 3 : ℝ) ^ (h + 1)) = (2 / 3) ^ (h + 1)
    rw [if_neg (show ¬ (h + n - 3 < h) by omega), if_neg (show ¬ (h + n - 3 < h + n - 3) by omega)]
  have hα0 : 0 < α := by
    by_contra hc
    push_neg at hc
    have : α * (2 / 3 : ℝ) ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    have : (0 : ℝ) < (2 / 3) ^ (h + 1) := by positivity
    linarith
  have := mul_le_mul_of_nonneg_left (le_trans (hev j2) hbig) hα0.le
  linarith

theorem op562nc_geom (h : ℕ) :
    ∑ k ∈ Finset.range h, (2 / 3 : ℝ) ^ (k + 1) = 2 - 2 * (2 / 3 : ℝ) ^ h := by
  induction h with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem op562nc_T (h n : ℕ) (hn : 3 ≤ n) :
    additive_valuation (op562nc_W h n) (Finset.univ.filter (fun t : Fin (h + n - 2) => t.val < h))
      = 2 - 2 * (2 / 3 : ℝ) ^ h := by
  unfold additive_valuation
  rw [Finset.sum_filter]
  have : ∀ t : Fin (h + n - 2), (if t.val < h then op562nc_W h n t else 0) =
      (fun k : ℕ => if k < h then (2 / 3 : ℝ) ^ (k + 1) else 0) t.val := by
    intro t
    simp only [op562nc_W]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun t _ => this t)]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < h then (2 / 3 : ℝ) ^ (k + 1) else 0)]
  rw [← Finset.sum_filter]
  have hr : (Finset.range (h + n - 2)).filter (fun k => k < h) = Finset.range h := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hr, op562nc_geom]

theorem op562nc_WQ (h n : ℕ) (g : Fin (h + n - 2)) (hg : g.val < h) :
    op562nc_W h n g = (2 / 3 : ℝ) ^ (g.val + 1) := by
  simp [op562nc_W, hg]

/-- In a 1-EEFX bundle for the exact profile, an agent holding only small goods and worth
less than 1 must see all other small goods in one part. -/
theorem op562nc_K (h n : ℕ) (hn : 3 ≤ n) (S : Finset (Fin (h + n - 2)))
    (hbund : is_alpha_eefx_bundle (additive_valuation (op562nc_W h n)) n 1 S)
    (hSQ : ∀ t ∈ S, t.val < h) (hx : additive_valuation (op562nc_W h n) S < 1) :
    ∀ g : Fin (h + n - 2), g.val < h → g ∉ S →
      2 - 2 * (2 / 3 : ℝ) ^ h - additive_valuation (op562nc_W h n) S - op562nc_W h n g
        ≤ additive_valuation (op562nc_W h n) S := by
  classical
  obtain ⟨Y, hdisj, hY, hefx⟩ := hbund
  set av := additive_valuation (op562nc_W h n) with hav
  have hcov : ∀ x, x ∉ S → ∃ p, x ∈ Y p := by
    intro x hx
    have : x ∈ Finset.biUnion Finset.univ Y := by
      rw [hY]; simp [hx]
    simpa using this
  intro g hg hgS
  obtain ⟨p, hp⟩ := hcov g hgS
  have hall : ∀ g' : Fin (h + n - 2), g'.val < h → g' ∉ S → g' ∈ Y p := by
    intro g' hg' hg'S
    by_cases hgg : g' = g
    · rw [hgg]; exact hp
    have hgv : g'.val ≠ g.val := fun h => hgg (Fin.ext h)
    let e : Fin n → Fin (h + n - 2) := fun j =>
      if hj : j.val < n - 3 then ⟨h + j.val, by omega⟩
      else if j.val = n - 3 then ⟨h + n - 3, by omega⟩
      else if j.val = n - 2 then g else g'
    have hev : ∀ j : Fin n, (e j).val = if j.val < n - 3 then h + j.val
        else if j.val = n - 3 then h + n - 3 else if j.val = n - 2 then g.val else g'.val := by
      intro j; simp only [e]; split_ifs <;> rfl
    have he : Function.Injective e := by
      intro a b hab
      have := congrArg Fin.val hab
      rw [hev, hev] at this
      apply Fin.ext
      split_ifs at this <;> omega
    have heS : ∀ j, e j ∉ S := by
      intro j hj
      have hv := hev j
      split_ifs at hv with c1 c2 c3
      · have := hSQ _ hj; omega
      · have := hSQ _ hj; omega
      · have : e j = g := Fin.ext hv
        exact hgS (this ▸ hj)
      · have : e j = g' := Fin.ext hv
        exact hg'S (this ▸ hj)
    obtain ⟨p', j1, j2, hne, h1, h2⟩ := op562nc_pigeon hn Y S hY e he heS
    have hbig : ∀ j, j.val < n - 2 → 1 ≤ op562nc_W h n (e j) := by
      intro j hj
      have hge : h ≤ (e j).val := by rw [hev]; split_ifs <;> omega
      unfold op562nc_W
      rw [if_neg (by omega)]
      split_ifs <;> norm_num
    have hsmall : ∀ ja jb, ja ≠ jb → e ja ∈ Y p' → e jb ∈ Y p' → jb.val < n - 2 → False := by
      intro ja jb hab ha hb hjb
      have h1' := hefx p' (e ja) ha
      have h2' := op562nc_two_in_part (op562nc_W h n) (op562nc_W_nonneg h n) (Y p')
        (fun h => hab (he h)) ha hb
      have := hbig jb hjb
      simp only [one_mul] at h1'
      linarith
    have hj1 : n - 2 ≤ j1.val := by
      by_contra hc; exact hsmall j2 j1 (Ne.symm hne) h2 h1 (by omega)
    have hj2 : n - 2 ≤ j2.val := by
      by_contra hc; exact hsmall j1 j2 hne h1 h2 (by omega)
    have hg_in : g ∈ Y p' ∧ g' ∈ Y p' := by
      have hv : (j1.val = n - 2 ∧ j2.val = n - 1) ∨ (j1.val = n - 1 ∧ j2.val = n - 2) := by
        have := j1.isLt; have := j2.isLt
        have : j1.val ≠ j2.val := fun h => hne (Fin.ext h)
        omega
      rcases hv with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have e1 : e j1 = g := Fin.ext (by rw [hev]; split_ifs <;> omega)
        have e2 : e j2 = g' := Fin.ext (by rw [hev]; split_ifs <;> omega)
        rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2⟩
      · have e1 : e j2 = g := Fin.ext (by rw [hev]; split_ifs <;> omega)
        have e2 : e j1 = g' := Fin.ext (by rw [hev]; split_ifs <;> omega)
        rw [e1] at h2; rw [e2] at h1; exact ⟨h2, h1⟩
    have hpp : p = p' := by
      by_contra hc
      have := hdisj p p' hc
      exact Finset.disjoint_left.mp this hp hg_in.1
    rw [hpp]; exact hg_in.2
  set Q := Finset.univ.filter (fun t : Fin (h + n - 2) => t.val < h) with hQ
  have hSsub : S ⊆ Q := by
    intro t ht; simp [hQ, hSQ t ht]
  have hgQ : g ∈ Q \ S := by simp [hQ, hg, hgS]
  have hsub : (Q \ S).erase g ⊆ (Y p).erase g := by
    intro t ht
    rw [Finset.mem_erase] at ht ⊢
    refine ⟨ht.1, ?_⟩
    have ht2 := ht.2
    rw [Finset.mem_sdiff] at ht2
    exact hall t (by simpa [hQ] using ht2.1) ht2.2
  have h1 := op562nc_av_mono (op562nc_W h n) (op562nc_W_nonneg h n) hsub
  have h2 := hefx p g hp
  have h3 : av ((Q \ S).erase g) = av Q - av S - op562nc_W h n g := by
    simp only [hav, additive_valuation]
    rw [Finset.sum_erase_eq_sub hgQ, Finset.sum_sdiff_eq_sub hSsub]
  have hT : av Q = 2 - 2 * (2 / 3 : ℝ) ^ h := by
    rw [hav, hQ]; exact op562nc_T h n hn
  rw [one_mul] at h2
  linarith

/-- Three-adic separation: inside the small goods other than the smallest, the sum of a set
times `3^(h-1)` is `2^(h-1)` mod 3 when it contains the second smallest good, else 0. -/
theorem op562nc_three_adic (h n : ℕ) (hh : 2 ≤ h) (X : Finset (Fin (h + n - 2)))
    (hX : ∀ t ∈ X, t.val < h - 1) :
    ∃ N : ℕ, (3 : ℝ) ^ (h - 1) * additive_valuation (op562nc_W h n) X = N ∧
      (N : ZMod 3) = if (∃ t ∈ X, t.val = h - 2) then (2 : ZMod 3) ^ (h - 1) else 0 := by
  classical
  refine ⟨∑ t ∈ X, 2 ^ (t.val + 1) * 3 ^ (h - 2 - t.val), ?_, ?_⟩
  · unfold additive_valuation
    rw [Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := hX t ht
    rw [op562nc_WQ h n t (by omega)]
    have he : h - 1 = (h - 2 - t.val) + (t.val + 1) := by omega
    rw [he, pow_add, div_pow]
    field_simp
    try ring
  · push_cast
    have hterm : ∀ t ∈ X, ((2 : ZMod 3) ^ (t.val + 1) * (3 : ZMod 3) ^ (h - 2 - t.val)) =
        if t.val = h - 2 then (2 : ZMod 3) ^ (h - 1) else 0 := by
      intro t ht
      have ht' := hX t ht
      split_ifs with heq
      · rw [heq, Nat.sub_self, pow_zero, mul_one]; congr 1; omega
      · have : (3 : ZMod 3) = 0 := by decide
        rw [this, zero_pow (by omega), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const]
    by_cases hex : ∃ t ∈ X, t.val = h - 2
    · rw [if_pos hex]
      obtain ⟨t0, ht0, ht0v⟩ := hex
      have hcard : (X.filter (fun t => t.val = h - 2)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨t0, ?_⟩
        ext t
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, htv⟩; exact Fin.ext (by omega)
        · rintro rfl; exact ⟨ht0, ht0v⟩
      rw [hcard]; simp
    · rw [if_neg hex]
      have hcard : (X.filter (fun t => t.val = h - 2)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro t ht htv; exact hex ⟨t, ht, htv⟩
      rw [hcard]; simp

theorem op562nc_two_ne : (2 : ZMod 3) ≠ 0 := by decide

theorem op562nc_two_pow_ne (k : ℕ) : (2 : ZMod 3) ^ k ≠ 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact pow_ne_zero _ op562nc_two_ne

/-- The small-goods lemma for one agent: either worth at least 1, or the 2-part bound. -/
def op562nc_Kp (h n : ℕ) (S : Finset (Fin (h + n - 2))) : Prop :=
  (∀ t ∈ S, t.val < h) ∧ (1 ≤ additive_valuation (op562nc_W h n) S ∨
    ∀ g : Fin (h + n - 2), g.val < h → g ∉ S →
      2 - 2 * (2 / 3 : ℝ) ^ h - additive_valuation (op562nc_W h n) S - op562nc_W h n g
        ≤ additive_valuation (op562nc_W h n) S)

theorem op562nc_av_union (h n : ℕ) {A B : Finset (Fin (h + n - 2))} (hAB : Disjoint A B) :
    additive_valuation (op562nc_W h n) (A ∪ B) =
      additive_valuation (op562nc_W h n) A + additive_valuation (op562nc_W h n) B := by
  unfold additive_valuation; exact Finset.sum_union hAB

theorem op562nc_av_le_T (h n : ℕ) (hn : 3 ≤ n) {A : Finset (Fin (h + n - 2))}
    (hA : ∀ t ∈ A, t.val < h) :
    additive_valuation (op562nc_W h n) A ≤ 2 - 2 * (2 / 3 : ℝ) ^ h := by
  rw [← op562nc_T h n hn]
  apply op562nc_av_mono _ (op562nc_W_nonneg h n)
  intro t ht; simp [hA t ht]

theorem op562nc_single_le (h n : ℕ) {A : Finset (Fin (h + n - 2))} {t : Fin (h + n - 2)}
    (ht : t ∈ A) : op562nc_W h n t ≤ additive_valuation (op562nc_W h n) A := by
  unfold additive_valuation
  exact Finset.single_le_sum (f := op562nc_W h n) (fun _ _ => op562nc_W_nonneg h n _) ht

/-- No three disjoint bundles of small goods, two avoiding the smallest good, satisfy the bound. -/
theorem op562nc_three_aux (h n : ℕ) (hn : 3 ≤ n) (hh : 3 ≤ h)
    (S1 S2 S3 : Finset (Fin (h + n - 2)))
    (h12 : Disjoint S1 S2) (h13 : Disjoint S1 S3) (h23 : Disjoint S2 S3)
    (K1 : op562nc_Kp h n S1) (K2 : op562nc_Kp h n S2) (K3 : op562nc_Kp h n S3)
    (hd1 : ∀ t ∈ S1, t.val ≠ h - 1) (hd2 : ∀ t ∈ S2, t.val ≠ h - 1) : False := by
  classical
  have hδpos : (0 : ℝ) < (2 / 3 : ℝ) ^ h := by positivity
  have hδsmall : (2 / 3 : ℝ) ^ h ≤ 8 / 27 := by
    have : (2 / 3 : ℝ) ^ h ≤ (2 / 3) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hh
    linarith [show ((2 : ℝ) / 3) ^ 3 = 8 / 27 by norm_num]
  let d : Fin (h + n - 2) := ⟨h - 1, by omega⟩
  have hWd : op562nc_W h n d = (2 / 3 : ℝ) ^ h := by
    rw [op562nc_WQ h n d (by show h - 1 < h; omega)]; show (2 / 3 : ℝ) ^ (h - 1 + 1) = (2 / 3) ^ h; congr 1; omega
  have hlow : ∀ S, op562nc_Kp h n S → (∀ t ∈ S, t.val ≠ h - 1) →
      (2 - 2 * (2 / 3 : ℝ) ^ h - (2 / 3 : ℝ) ^ h) / 2 ≤ additive_valuation (op562nc_W h n) S := by
    intro S K hd
    rcases K.2 with h1 | h1
    · linarith
    · have := h1 d (by show h - 1 < h; omega) (fun hm => hd d hm rfl)
      rw [hWd] at this; linarith
  have hx1 := hlow S1 K1 hd1
  have hx2 := hlow S2 K2 hd2
  have hsum : additive_valuation (op562nc_W h n) S1 + additive_valuation (op562nc_W h n) S2
      + additive_valuation (op562nc_W h n) S3 ≤ 2 - 2 * (2 / 3 : ℝ) ^ h := by
    have hu := op562nc_av_le_T h n hn (A := S1 ∪ S2 ∪ S3) (by
      intro t ht
      simp only [Finset.mem_union] at ht
      rcases ht with (ht | ht) | ht
      · exact K1.1 t ht
      · exact K2.1 t ht
      · exact K3.1 t ht)
    rw [op562nc_av_union h n (Finset.disjoint_union_left.mpr ⟨h13, h23⟩),
      op562nc_av_union h n h12] at hu
    linarith
  have hx3 : additive_valuation (op562nc_W h n) S3 ≤ (2 / 3 : ℝ) ^ h := by linarith
  have hS3 : ∀ t ∈ S3, t.val = h - 1 := by
    intro t ht
    by_contra hne
    have htl := K3.1 t ht
    have h1 := op562nc_single_le h n ht
    rw [op562nc_WQ h n t htl] at h1
    have h3 : (2 / 3 : ℝ) ^ (h - 1) ≤ (2 / 3) ^ (t.val + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (2 / 3 : ℝ) ^ h = (2 / 3) ^ (h - 1) * (2 / 3) := by
      rw [← pow_succ]; congr 1; omega
    have h4 : (0 : ℝ) < (2 / 3) ^ (h - 1) := by positivity
    linarith
  rcases K3.2 with h1 | h1
  · linarith
  · let e : Fin (h + n - 2) := ⟨h - 2, by omega⟩
    have h5 := h1 e (by show h - 2 < h; omega) (fun hm => by have := hS3 e hm; change h - 2 = h - 1 at this; omega)
    rw [op562nc_WQ h n e (by show h - 2 < h; omega)] at h5
    have h2 : (2 / 3 : ℝ) ^ h = (2 / 3) ^ (e.val + 1) * (2 / 3) := by
      rw [← pow_succ]; show (2 / 3 : ℝ) ^ h = (2 / 3) ^ (h - 2 + 1 + 1); congr 1; omega
    have h4 : (0 : ℝ) < (2 / 3) ^ (e.val + 1) := by positivity
    linarith

theorem op562nc_three (h n : ℕ) (hn : 3 ≤ n) (hh : 3 ≤ h)
    (S1 S2 S3 : Finset (Fin (h + n - 2)))
    (h12 : Disjoint S1 S2) (h13 : Disjoint S1 S3) (h23 : Disjoint S2 S3)
    (K1 : op562nc_Kp h n S1) (K2 : op562nc_Kp h n S2) (K3 : op562nc_Kp h n S3) : False := by
  -- at most one of the three contains the smallest good
  by_cases c1 : ∀ t ∈ S1, t.val ≠ h - 1
  · by_cases c2 : ∀ t ∈ S2, t.val ≠ h - 1
    · exact op562nc_three_aux h n hn hh S1 S2 S3 h12 h13 h23 K1 K2 K3 c1 c2
    · have c3 : ∀ t ∈ S3, t.val ≠ h - 1 := by
        intro t ht htv
        push_neg at c2
        obtain ⟨t', ht', ht'v⟩ := c2
        have : t = t' := Fin.ext (by omega)
        subst this
        exact Finset.disjoint_left.mp h23 ht' ht
      exact op562nc_three_aux h n hn hh S1 S3 S2 h13 h12 h23.symm K1 K3 K2 c1 c3
  · push_neg at c1
    obtain ⟨t1, ht1, ht1v⟩ := c1
    have hother : ∀ S, Disjoint S1 S → ∀ t ∈ S, t.val ≠ h - 1 := by
      intro S hS t ht htv
      have : t = t1 := Fin.ext (by omega)
      subst this
      exact Finset.disjoint_left.mp hS ht1 ht
    exact op562nc_three_aux h n hn hh S2 S3 S1 h23 h12.symm h13.symm K2 K3 K1
      (hother S2 h12) (hother S3 h13)

/-- Two disjoint bundles of small goods satisfying the bound cover all small goods. -/
theorem op562nc_two (h n : ℕ) (hn : 3 ≤ n) (hh : 3 ≤ h)
    (Sb Sc : Finset (Fin (h + n - 2))) (hbc : Disjoint Sb Sc)
    (Kb : op562nc_Kp h n Sb) (Kc : op562nc_Kp h n Sc) :
    ∀ g : Fin (h + n - 2), g.val < h → g ∈ Sb ∨ g ∈ Sc := by
  classical
  set av := additive_valuation (op562nc_W h n) with hav
  set Q := Finset.univ.filter (fun t : Fin (h + n - 2) => t.val < h) with hQ
  have hδpos : (0 : ℝ) < (2 / 3 : ℝ) ^ h := by positivity
  have hWpos : ∀ g, g.val < h → 0 < op562nc_W h n g := by
    intro g hg; rw [op562nc_WQ h n g hg]; positivity
  by_contra hcon
  push_neg at hcon
  obtain ⟨g0, hg0, hg0b, hg0c⟩ := hcon
  set R := Q \ (Sb ∪ Sc) with hR
  have hsubQ : Sb ∪ Sc ⊆ Q := by
    intro t ht
    simp only [Finset.mem_union] at ht
    simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ht with ht | ht
    · exact Kb.1 t ht
    · exact Kc.1 t ht
  have hRval : av R = 2 - 2 * (2 / 3 : ℝ) ^ h - av Sb - av Sc := by
    have hT : av Q = 2 - 2 * (2 / 3 : ℝ) ^ h := by rw [hav, hQ]; exact op562nc_T h n hn
    rw [← hT]
    have := op562nc_av_union h n hbc
    rw [← hav] at this
    have h2 : av R = av Q - av (Sb ∪ Sc) := by
      simp only [hR, hav, additive_valuation]
      rw [Finset.sum_sdiff_eq_sub hsubQ]
    rw [h2, this]; ring
  have hmemR : ∀ g, g.val < h → g ∉ Sb → g ∉ Sc → g ∈ R := by
    intro g hg h1 h2
    simp [hR, hQ, hg, h1, h2]
  have hRge : ∀ g, g ∈ R → op562nc_W h n g ≤ av R := fun g hg => op562nc_single_le h n hg
  have hRtwo : ∀ g g', g ∈ R → g' ∈ R → g ≠ g' →
      op562nc_W h n g + op562nc_W h n g' ≤ av R := by
    intro g g' hg hg' hne
    have hsub : ({g, g'} : Finset _) ⊆ R := by
      intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have := op562nc_av_mono (op562nc_W h n) (op562nc_W_nonneg h n) hsub
    simp only [additive_valuation] at this ⊢
    rwa [Finset.sum_pair hne] at this
  have hg0R := hmemR g0 hg0 hg0b hg0c
  have hW0 := hWpos g0 hg0
  have hbnd : ∀ S, op562nc_Kp h n S → av S < 1 →
      ∀ g, g.val < h → g ∉ S → 2 - 2 * (2 / 3 : ℝ) ^ h - av S - op562nc_W h n g ≤ av S := by
    intro S K hS
    rcases K.2 with h1 | h1
    · linarith
    · exact h1
  have hl := hRge g0 hg0R
  -- both bundles are worth less than 1
  have hb1 : av Sb < 1 := by
    by_contra hc
    push_neg at hc
    have hc1 : av Sc < 1 := by linarith
    have := hbnd Sc Kc hc1 g0 hg0 hg0c
    linarith
  have hc1 : av Sc < 1 := by
    by_contra hc
    push_neg at hc
    have := hbnd Sb Kb hb1 g0 hg0 hg0b
    linarith
  have Bb := hbnd Sb Kb hb1
  have Bc := hbnd Sc Kc hc1
  have e1 := Bb g0 hg0 hg0b
  have e2 := Bc g0 hg0 hg0c
  -- the rest is exactly `g0`, and the two bundles are worth the same
  have hReq : av R = op562nc_W h n g0 := by linarith
  have hxy : av Sb = av Sc := by linarith
  -- every other small good lies in a bundle and is worth at least `g0`
  have hcover : ∀ g, g.val < h → g ≠ g0 → g ∈ Sb ∨ g ∈ Sc := by
    intro g hg hne
    by_contra hc
    push_neg at hc
    have := hRtwo g0 g hg0R (hmemR g hg hc.1 hc.2) (Ne.symm hne)
    have := hWpos g hg
    linarith
  have hge : ∀ g, g.val < h → g ≠ g0 → op562nc_W h n g0 ≤ op562nc_W h n g := by
    intro g hg hne
    rcases hcover g hg hne with hgb | hgc
    · have hgc : g ∉ Sc := fun hm => Finset.disjoint_left.mp hbc hgb hm
      have := Bc g hg hgc; linarith
    · have hgb : g ∉ Sb := fun hm => Finset.disjoint_left.mp hbc hm hgc
      have := Bb g hg hgb; linarith
  -- so `g0` is the smallest good
  have hg0d : g0.val = h - 1 := by
    by_contra hne
    let d : Fin (h + n - 2) := ⟨h - 1, by omega⟩
    have hdv : d.val = h - 1 := rfl
    have h1 := hge d (by rw [hdv]; omega) (fun hm => hne (by rw [← hm]))
    rw [op562nc_WQ h n d (by rw [hdv]; omega), op562nc_WQ h n g0 hg0, hdv] at h1
    have h2 : (2 / 3 : ℝ) ^ (h - 1 + 1) < (2 / 3) ^ (g0.val + 1) :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  -- three-adic contradiction on the second smallest good
  have hXb : ∀ t ∈ Sb, t.val < h - 1 := by
    intro t ht
    have := Kb.1 t ht
    have : t ≠ g0 := fun he => hg0b (he ▸ ht)
    have : t.val ≠ g0.val := fun he => this (Fin.ext he)
    omega
  have hXc : ∀ t ∈ Sc, t.val < h - 1 := by
    intro t ht
    have := Kc.1 t ht
    have : t ≠ g0 := fun he => hg0c (he ▸ ht)
    have : t.val ≠ g0.val := fun he => this (Fin.ext he)
    omega
  obtain ⟨Nb, hNb, hNbm⟩ := op562nc_three_adic h n (by omega) Sb hXb
  obtain ⟨Nc, hNc, hNcm⟩ := op562nc_three_adic h n (by omega) Sc hXc
  have hN : Nb = Nc := by
    have : (Nb : ℝ) = Nc := by
      rw [← hNb, ← hNc]; exact congrArg (fun x => (3 : ℝ) ^ (h - 1) * x) hxy
    exact_mod_cast this
  let e : Fin (h + n - 2) := ⟨h - 2, by omega⟩
  have hne : e ≠ g0 := fun he => by
    have := congrArg Fin.val he; change h - 2 = g0.val at this; omega
  have hz := op562nc_two_pow_ne (h - 1)
  rcases hcover e (by show h - 2 < h; omega) hne with heb | hec
  · have hnc : ¬ ∃ t ∈ Sc, t.val = h - 2 := by
      rintro ⟨t, ht, htv⟩
      have : t = e := Fin.ext (by show t.val = h - 2; omega)
      exact Finset.disjoint_left.mp hbc heb (this ▸ ht)
    rw [if_pos ⟨e, heb, rfl⟩] at hNbm
    rw [if_neg hnc] at hNcm
    rw [hN, hNcm] at hNbm
    exact hz hNbm.symm
  · have hnb : ¬ ∃ t ∈ Sb, t.val = h - 2 := by
      rintro ⟨t, ht, htv⟩
      have : t = e := Fin.ext (by show t.val = h - 2; omega)
      exact Finset.disjoint_left.mp hbc (this ▸ ht) hec
    rw [if_pos ⟨e, hec, rfl⟩] at hNcm
    rw [if_neg hnb] at hNbm
    rw [hN] at hNbm
    rw [hNbm] at hNcm
    exact hz hNcm.symm

theorem op562nc_bundle_disj {m n : ℕ} (σ : Fin m → Fin n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (bundle_of σ i) (bundle_of σ j) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
  exact hij (ht1.symm.trans ht2)

/-- Consistency on the exact profile forces the owner of the last good to own nothing else. -/
theorem op562nc_force (h n : ℕ) (hn : 3 ≤ n) (hh : 3 ≤ h) (σ : Fin (h + n - 2) → Fin n)
    (hσ : is_alpha_eefx_allocation (fun _ => additive_valuation (op562nc_W h n)) 1 σ) :
    ∀ t : Fin (h + n - 2), t.val ≠ h + n - 3 → σ t ≠ σ ⟨h + n - 3, by omega⟩ := by
  classical
  set L : Fin (h + n - 2) := ⟨h + n - 3, by omega⟩ with hL
  have hLv : L.val = h + n - 3 := rfl
  let Jfree : Fin n → Prop := fun i =>
    ∀ j : Fin (h + n - 2), h ≤ j.val → j.val < h + n - 3 → σ j ≠ i
  have hK : ∀ i, Jfree i → σ L ≠ i → op562nc_Kp h n (bundle_of σ i) := by
    intro i hJ hLi
    have hQ : ∀ t ∈ bundle_of σ i, t.val < h := by
      intro t ht
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      by_contra hc
      have := t.isLt
      by_cases ht2 : t.val < h + n - 3
      · exact hJ t (by omega) ht2 ht
      · have : t = L := Fin.ext (by rw [hLv]; omega)
        exact hLi (this ▸ ht)
    refine ⟨hQ, ?_⟩
    by_cases h1 : 1 ≤ additive_valuation (op562nc_W h n) (bundle_of σ i)
    · exact Or.inl h1
    · exact Or.inr (op562nc_K h n hn _ (hσ i) hQ (by linarith))
  have hcount : 2 < (Finset.univ.filter Jfree).card := by
    have hA : (Finset.univ.filter (fun i => ¬ Jfree i)) ⊆
        Finset.univ.image (fun j : Fin (n - 3) => σ ⟨h + j.val, by omega⟩) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Jfree] at hi
      push_neg at hi
      obtain ⟨j, hj1, hj2, hj3⟩ := hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨j.val - h, by omega⟩, ?_⟩
      rw [← hj3]
      congr 1
      exact Fin.ext (by show h + (j.val - h) = j.val; omega)
    have h1 := Finset.card_le_card hA
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n - 3))))
      (f := fun j : Fin (n - 3) => σ ⟨h + j.val, by omega⟩)
    have h3 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) Jfree
    simp only [Finset.card_univ, Fintype.card_fin] at h2 h3
    omega
  obtain ⟨b1, hb1, b2, hb2, b3, hb3, h12, h13, h23⟩ := Finset.two_lt_card.mp hcount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1 hb2 hb3
  have hfin : ∀ a b c, Jfree a → Jfree b → Jfree c → a ≠ b → a ≠ c → b ≠ c → σ L = a →
      ∀ t : Fin (h + n - 2), t.val ≠ h + n - 3 → σ t ≠ a := by
    intro a b c ha hb hc hab hac hbc hLa t ht hta
    have hcov := op562nc_two h n hn hh (bundle_of σ b) (bundle_of σ c)
      (op562nc_bundle_disj σ hbc) (hK b hb (by rw [hLa]; exact hab))
      (hK c hc (by rw [hLa]; exact hac))
    by_cases htl : t.val < h
    · rcases hcov t htl with h1 | h1 <;>
        simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      · exact hab (hta.symm.trans h1)
      · exact hac (hta.symm.trans h1)
    · exact ha t (by omega) (by have := t.isLt; omega) hta
  intro t ht
  by_cases c1 : σ L = b1
  · rw [c1]; exact hfin b1 b2 b3 hb1 hb2 hb3 h12 h13 h23 c1 t ht
  by_cases c2 : σ L = b2
  · rw [c2]; exact hfin b2 b1 b3 hb2 hb1 hb3 (Ne.symm h12) h23 h13 c2 t ht
  by_cases c3 : σ L = b3
  · rw [c3]; exact hfin b3 b1 b2 hb3 hb1 hb2 (Ne.symm h13) (Ne.symm h23) h12 c3 t ht
  exact (op562nc_three h n hn hh _ _ _ (op562nc_bundle_disj σ h12) (op562nc_bundle_disj σ h13)
    (op562nc_bundle_disj σ h23) (hK b1 hb1 c1) (hK b2 hb2 c2) (hK b3 hb3 c3)).elim

/-- For n >= 3, no consistent online algorithm guarantees positive EEFX approximation for error factor rho >= 3/2. -/
theorem op562_not_consistent_eefx_of_ge_three_halves (n : ℕ) (hn : 3 ≤ n) (ρ : ℝ)
    (hρ : 3 / 2 ≤ ρ) :
    ¬ has_consistent_eefx_algorithm n ρ := by
  rintro ⟨alg, α, hα, hon, hcons, hguar⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < α * (2 / 3 : ℝ) ^ 3 by positivity)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  have hh : 3 ≤ k + 3 := by omega
  have hsmall : (2 / 3 : ℝ) ^ (k + 3 + 1) < α * (2 / 3) ^ 3 :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk
  have hσ := hcons (k + 3 + n - 2) (fun _ => op562nc_W (k + 3) n) (fun _ => op562nc_W (k + 3) n)
    (fun _ g => op562nc_W_nonneg (k + 3) n g) (fun _ => rfl)
  have hσ' := hguar (k + 3 + n - 2) (fun _ => op562nc_V (k + 3) n)
    (fun _ => op562nc_W (k + 3) n) (fun _ g => op562nc_V_nonneg (k + 3) n g)
    (op562nc_overestimate (k + 3) n hn ρ hρ)
  have hsame : ∀ t : Fin (k + 3 + n - 2), t.val ≠ k + 3 + n - 3 →
      alg (k + 3 + n - 2) (fun _ => op562nc_W (k + 3) n) (fun _ => op562nc_V (k + 3) n) t =
      alg (k + 3 + n - 2) (fun _ => op562nc_W (k + 3) n) (fun _ => op562nc_W (k + 3) n) t := by
    intro t ht
    apply hon
    intro s hs i
    show op562nc_V (k + 3) n s = op562nc_W (k + 3) n s
    have hs' : s.val ≤ t.val := hs
    have : s.val < k + 3 + n - 3 := by have := t.isLt; omega
    unfold op562nc_V op562nc_W
    split_ifs <;> first | rfl | omega
  have hforce := op562nc_force (k + 3) n hn hh _ hσ
  refine op562nc_fail (k + 3) n hn hh α hsmall _ ?_ (hσ' (alg (k + 3 + n - 2)
    (fun _ => op562nc_W (k + 3) n) (fun _ => op562nc_W (k + 3) n) ⟨k + 3 + n - 3, by omega⟩))
  intro t ht
  simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  by_contra hne
  exact hforce t hne (by rw [← hsame t hne]; exact ht)
