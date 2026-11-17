import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorizationCoarsening
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.SetOfIsNatFactorizationFinite

/-!
# factorization_coarsening_signed_orderings_sum_zero

Topic: combinatorics   Node: 7dc65e1e5db9

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

Lemma 5 of arXiv:2611.18194 in multiplicative form: if W is a multiset of at least two integers > 1 whose product is divisible by the prime q exactly once (W is pointed), then Σ over all coarsenings y of W of (-1)^{|y|-1} N(y) = 0, where N(y) = (|y|-1)!/(c_1!⋯c_s!) and c_i are the multiplicities of the distinct elements of y not divisible by q.
-/

namespace FactMobL5

noncomputable def fw (q : ℕ) (y : Multiset ℕ) : ℚ :=
  (-1 : ℚ) ^ (y.card - 1) * ((y.card - 1).factorial : ℚ) /
    ∏ a ∈ (y.filter (fun a => ¬ q ∣ a)).toFinset,
      (((y.filter (fun a => ¬ q ∣ a)).count a).factorial : ℚ)

noncomputable def P (z : Multiset ℕ) : ℚ := ∏ a ∈ z.toFinset, ((z.count a).factorial : ℚ)

lemma P_pos (z : Multiset ℕ) : 0 < P z :=
  Finset.prod_pos (fun a _ => by exact_mod_cast Nat.factorial_pos _)

lemma P_cons (v : ℕ) (z : Multiset ℕ) : P (v ::ₘ z) = ((z.count v + 1 : ℕ) : ℚ) * P z := by
  unfold P
  have hsub : z.toFinset ⊆ (v ::ₘ z).toFinset := by
    intro a ha; simp only [Multiset.mem_toFinset] at ha ⊢; exact Multiset.mem_cons_of_mem ha
  rw [Finset.prod_subset (f := fun a => ((z.count a).factorial : ℚ)) hsub (fun a _ ha => by
    rw [Multiset.count_eq_zero.2 (fun h => ha (Multiset.mem_toFinset.2 h))]; simp)]
  have hv : v ∈ (v ::ₘ z).toFinset := by simp
  rw [← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ (fun a => ((z.count a).factorial : ℚ)) hv]
  rw [Multiset.count_cons_self, Nat.factorial_succ]
  rw [Finset.prod_congr rfl (fun a ha => by
    have : a ≠ v := Finset.ne_of_mem_erase ha
    rw [Multiset.count_cons_of_ne this])]
  push_cast; ring

lemma one_lt_prod_of {g : Multiset ℕ} (hg : g ≠ 0) (h : ∀ a ∈ g, 1 < a) : 1 < g.prod := by
  induction g using Multiset.induction_on with
  | empty => exact absurd rfl hg
  | cons a g ih =>
    rw [Multiset.prod_cons]
    have ha := h a (Multiset.mem_cons_self a g)
    have hp : 0 < g.prod := Multiset.prod_pos (fun b hb => by
      have := h b (Multiset.mem_cons_of_mem hb); omega)
    nlinarith

lemma le_join_of_mem {g : Multiset ℕ} {G : Multiset (Multiset ℕ)} (hg : g ∈ G) : g ≤ G.join := by
  obtain ⟨G0, rfl⟩ : ∃ G0, G = g ::ₘ G0 := ⟨G.erase g, (Multiset.cons_erase hg).symm⟩
  rw [Multiset.join_cons]; exact Multiset.le_add_right _ _

lemma coars_elems {x y : Multiset ℕ} (h : IsFactorizationCoarsening x y) :
    ∀ b ∈ y, ∃ g : Multiset ℕ, g ≠ 0 ∧ g ≤ x ∧ g.prod = b := by
  obtain ⟨G, hG0, hJ, hM⟩ := h
  intro b hb
  rw [← hM, Multiset.mem_map] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  exact ⟨g, hG0 g hg, hJ ▸ le_join_of_mem hg, rfl⟩

lemma coars_prod {x y : Multiset ℕ} (h : IsFactorizationCoarsening x y) : y.prod = x.prod := by
  obtain ⟨G, _, hJ, hM⟩ := h
  rw [← hM, ← hJ, Multiset.prod_join]

lemma coars_gt {x y : Multiset ℕ} (hx : ∀ a ∈ x, 1 < a) (h : IsFactorizationCoarsening x y) :
    ∀ b ∈ y, 1 < b := by
  intro b hb
  obtain ⟨g, hg0, hgx, rfl⟩ := coars_elems h b hb
  exact one_lt_prod_of hg0 (fun a ha => hx a (Multiset.mem_of_le hgx ha))

lemma coars_ndvd {q : ℕ} {x y : Multiset ℕ} (hx : ¬ q ∣ x.prod) (h : IsFactorizationCoarsening x y) :
    ∀ b ∈ y, ¬ q ∣ b := by
  intro b hb hqb
  obtain ⟨g, _, hgx, rfl⟩ := coars_elems h b hb
  exact hx (hqb.trans (Multiset.prod_dvd_prod_of_le hgx))

lemma coars_finite (W : Multiset ℕ) (hW : ∀ a ∈ W, 1 < a) :
    {y : Multiset ℕ | IsFactorizationCoarsening W y}.Finite :=
  (setOf_isNatFactorization_finite W.prod).subset (fun y hy => ⟨coars_gt hW hy, coars_prod hy⟩)

lemma coars_ne_zero {x y : Multiset ℕ} (hx : x ≠ 0) (h : IsFactorizationCoarsening x y) : y ≠ 0 := by
  obtain ⟨G, _, hJ, hM⟩ := h
  rintro rfl
  rw [Multiset.map_eq_zero] at hM
  subst hM; simp at hJ; exact hx hJ.symm

lemma C1 {w : ℕ} {W' y : Multiset ℕ} (h : IsFactorizationCoarsening (w ::ₘ W') y) :
    ∃ g' y' : Multiset ℕ, y = (w * g'.prod) ::ₘ y' ∧ g' ≤ W' ∧
      IsFactorizationCoarsening W' (if g' = 0 then y' else g'.prod ::ₘ y') := by
  obtain ⟨G, hG0, hJ, hM⟩ := h
  have hw : w ∈ G.join := by rw [hJ]; exact Multiset.mem_cons_self _ _
  obtain ⟨g, hg, hwg⟩ := Multiset.mem_join.1 hw
  obtain ⟨G0, rfl⟩ : ∃ G0, G = g ::ₘ G0 := ⟨G.erase g, (Multiset.cons_erase hg).symm⟩
  obtain ⟨g', rfl⟩ : ∃ g', g = w ::ₘ g' := ⟨g.erase w, (Multiset.cons_erase hwg).symm⟩
  simp only [Multiset.join_cons, Multiset.cons_add] at hJ
  have hW' : W' = g' + G0.join := (Multiset.cons_inj_right w).1 hJ.symm
  subst hW'
  refine ⟨g', G0.map Multiset.prod, ?_, Multiset.le_add_right _ _, ?_⟩
  · rw [← hM]; simp [Multiset.prod_cons]
  · have hG0' : ∀ h ∈ G0, h ≠ 0 := fun h hh => hG0 h (Multiset.mem_cons_of_mem hh)
    split_ifs with hg'
    · subst hg'; exact ⟨G0, hG0', by simp, rfl⟩
    · refine ⟨g' ::ₘ G0, ?_, by simp, by simp⟩
      intro h hh
      rcases Multiset.mem_cons.1 hh with rfl | hh
      · exact hg'
      · exact hG0' h hh

lemma C2a {w : ℕ} {W' z : Multiset ℕ} (h : IsFactorizationCoarsening W' z) :
    IsFactorizationCoarsening (w ::ₘ W') (w ::ₘ z) := by
  obtain ⟨G, hG0, hJ, hM⟩ := h
  refine ⟨{w} ::ₘ G, ?_, ?_, ?_⟩
  · intro h hh
    rcases Multiset.mem_cons.1 hh with rfl | hh
    · simp
    · exact hG0 h hh
  · simp [hJ]
  · simp [hM]

lemma C2b {w v : ℕ} {W' z : Multiset ℕ} (h : IsFactorizationCoarsening W' z) (hv : v ∈ z) :
    IsFactorizationCoarsening (w ::ₘ W') ((v * w) ::ₘ z.erase v) := by
  obtain ⟨G, hG0, hJ, hM⟩ := h
  subst hM hJ
  obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.1 hv
  obtain ⟨G0, rfl⟩ : ∃ G0, G = g ::ₘ G0 := ⟨G.erase g, (Multiset.cons_erase hg).symm⟩
  refine ⟨(w ::ₘ g) ::ₘ G0, ?_, ?_, ?_⟩
  · intro h hh
    rcases Multiset.mem_cons.1 hh with rfl | hh
    · simp
    · exact hG0 h (Multiset.mem_cons_of_mem hh)
  · simp
  · simp [Multiset.prod_cons, mul_comm]

lemma fw_none {q w : ℕ} (hqw : q ∣ w) {z : Multiset ℕ} (hz : ∀ b ∈ z, ¬ q ∣ b) :
    fw q (w ::ₘ z) = (-1 : ℚ) ^ z.card * (z.card.factorial : ℚ) / P z := by
  unfold fw
  rw [Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 hqw), Multiset.filter_eq_self.2 hz,
    Multiset.card_cons, Nat.add_sub_cancel]
  rfl

lemma fw_some {q w v : ℕ} (hqw : q ∣ w) {z : Multiset ℕ} (hz : ∀ b ∈ z, ¬ q ∣ b) (hv : v ∈ z) :
    fw q ((v * w) ::ₘ z.erase v) = (-1 : ℚ) ^ (z.card - 1) * ((z.card - 1).factorial : ℚ) / P (z.erase v) := by
  unfold fw
  rw [Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 (dvd_mul_of_dvd_right hqw v)),
    Multiset.filter_eq_self.2 (fun b hb => hz b (Multiset.mem_of_mem_erase hb)),
    Multiset.card_cons, Nat.add_sub_cancel, Multiset.card_erase_of_mem hv]
  rfl

lemma P_erase {v : ℕ} {z : Multiset ℕ} (hv : v ∈ z) : P z = ((z.count v : ℕ) : ℚ) * P (z.erase v) := by
  have h := P_cons v (z.erase v)
  rw [Multiset.cons_erase hv] at h
  rw [h]
  congr 2
  rw [← Multiset.count_cons_self v (z.erase v), Multiset.cons_erase hv]

lemma fibre_zero {q w : ℕ} (hqw : q ∣ w) {z : Multiset ℕ} (hz : ∀ b ∈ z, ¬ q ∣ b) (hz0 : z ≠ 0) :
    fw q (w ::ₘ z) + ∑ v ∈ z.toFinset, fw q ((v * w) ::ₘ z.erase v) = 0 := by
  rw [fw_none hqw hz, Finset.sum_congr rfl (fun v hv => fw_some hqw hz (Multiset.mem_toFinset.1 hv))]
  have hP := P_pos z
  have key : ∀ v ∈ z.toFinset, (-1 : ℚ) ^ (z.card - 1) * ((z.card - 1).factorial : ℚ) / P (z.erase v)
      = (-1 : ℚ) ^ (z.card - 1) * ((z.card - 1).factorial : ℚ) * ((z.count v : ℕ) : ℚ) / P z := by
    intro v hv
    have hv' := Multiset.mem_toFinset.1 hv
    have hc : ((z.count v : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Multiset.count_pos.2 hv').ne'
    have hPe := P_pos (z.erase v)
    rw [P_erase hv']
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum,
    Multiset.toFinset_sum_count_eq]
  obtain ⟨k, hk⟩ : ∃ k, z.card = k + 1 :=
    ⟨z.card - 1, by have := Multiset.card_pos.2 hz0; omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  field_simp
  push_cast
  ring

theorem lemma5 (q : ℕ) (hq : q.Prime)
    (W : Multiset ℕ) (hW : ∀ a ∈ W, 1 < a) (hdvd : q ∣ W.prod) (hsq : ¬ q ^ 2 ∣ W.prod)
    (hcard : 2 ≤ W.card) :
    ∑ᶠ (y : Multiset ℕ) (_ : IsFactorizationCoarsening W y), fw q y = 0 := by
  obtain ⟨w, hwW, hqw⟩ := hq.prime.exists_mem_multiset_dvd hdvd
  obtain ⟨W', rfl⟩ : ∃ W', W = w ::ₘ W' := ⟨W.erase w, (Multiset.cons_erase hwW).symm⟩
  have hW'q : ¬ q ∣ W'.prod := by
    intro h; apply hsq; rw [Multiset.prod_cons, pow_two]; exact mul_dvd_mul hqw h
  have hW'gt : ∀ a ∈ W', 1 < a := fun a ha => hW a (Multiset.mem_cons_of_mem ha)
  have hw1 : 1 < w := hW w (Multiset.mem_cons_self _ _)
  have hW'ne : W' ≠ 0 := by rintro rfl; simp at hcard
  have hfin := coars_finite _ hW
  have hfin' := coars_finite _ hW'gt
  have hmem : ∀ y, y ∈ hfin.toFinset ↔ IsFactorizationCoarsening (w ::ₘ W') y :=
    fun y => Set.Finite.mem_toFinset _
  have hmem' : ∀ z, z ∈ hfin'.toFinset ↔ IsFactorizationCoarsening W' z :=
    fun z => Set.Finite.mem_toFinset _
  change ∑ᶠ y ∈ {y | IsFactorizationCoarsening (w ::ₘ W') y}, fw q y = 0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  -- structure of a coarsening
  have hstruct : ∀ y, IsFactorizationCoarsening (w ::ₘ W') y → ∃ g' y' : Multiset ℕ,
      y = (w * g'.prod) ::ₘ y' ∧
      IsFactorizationCoarsening W' (if g' = 0 then y' else g'.prod ::ₘ y') ∧
      (∀ b ∈ y', ¬ q ∣ b) ∧ (g' ≠ 0 → 1 < g'.prod) := by
    intro y hy
    obtain ⟨g', y', rfl, hg'W, hco⟩ := C1 hy
    refine ⟨g', y', rfl, hco, ?_, fun h0 => one_lt_prod_of h0
      (fun a ha => hW'gt a (Multiset.mem_of_le hg'W ha))⟩
    intro b hb
    split_ifs at hco
    · exact coars_ndvd hW'q hco b hb
    · exact coars_ndvd hW'q hco b (Multiset.mem_cons_of_mem hb)
  let jj : (Σ _ : Multiset ℕ, Option ℕ) → Multiset ℕ :=
    fun p => p.2.elim (w ::ₘ p.1) (fun v => (v * w) ::ₘ p.1.erase v)
  let tt : Multiset ℕ → ℕ := fun y => (y.filter (fun a => q ∣ a)).prod
  let ii : Multiset ℕ → (Σ _ : Multiset ℕ, Option ℕ) := fun y =>
    if tt y = w then ⟨y.filter (fun a => ¬ q ∣ a), none⟩
    else ⟨(tt y / w) ::ₘ y.filter (fun a => ¬ q ∣ a), some (tt y / w)⟩
  have tt_eq : ∀ (t : ℕ) (y' : Multiset ℕ), q ∣ t → (∀ b ∈ y', ¬ q ∣ b) → tt (t ::ₘ y') = t := by
    intro t y' ht hy'
    simp only [tt]
    rw [Multiset.filter_cons_of_pos (p := fun a => q ∣ a) _ ht, Multiset.filter_eq_nil.2 hy']
    simp
  have filt_eq : ∀ (t : ℕ) (y' : Multiset ℕ), q ∣ t → (∀ b ∈ y', ¬ q ∣ b) →
      (t ::ₘ y').filter (fun a => ¬ q ∣ a) = y' := by
    intro t y' ht hy'
    rw [Multiset.filter_cons_of_neg (p := fun a => ¬ q ∣ a) _ (not_not.2 ht), Multiset.filter_eq_self.2 hy']
  have hii : ∀ y, IsFactorizationCoarsening (w ::ₘ W') y → ∃ g' y' : Multiset ℕ,
      y = (w * g'.prod) ::ₘ y' ∧
      IsFactorizationCoarsening W' (if g' = 0 then y' else g'.prod ::ₘ y') ∧
      (∀ b ∈ y', ¬ q ∣ b) ∧
      ii y = (if g' = 0 then ⟨y', none⟩ else ⟨g'.prod ::ₘ y', some g'.prod⟩) := by
    intro y hy
    obtain ⟨g', y', rfl, hco, hy', hg1⟩ := hstruct y hy
    refine ⟨g', y', rfl, hco, hy', ?_⟩
    have ht := tt_eq (w * g'.prod) y' (dvd_mul_of_dvd_left hqw _) hy'
    have hf := filt_eq (w * g'.prod) y' (dvd_mul_of_dvd_left hqw _) hy'
    simp only [ii, ht, hf]
    by_cases hg : g' = 0
    · subst hg; simp
    · have h1 := hg1 hg
      have hne : w * g'.prod ≠ w := by
        intro h; have : w * g'.prod > w * 1 := Nat.mul_lt_mul_of_pos_left h1 (by omega)
        omega
      rw [if_neg hne, if_neg hg, Nat.mul_div_cancel_left _ (by omega : 0 < w)]
  rw [Finset.sum_nbij' ii jj (t := hfin'.toFinset.sigma (fun z => Finset.insertNone z.toFinset))
    (g := fun p => fw q (jj p))]
  · rw [Finset.sum_sigma]
    apply Finset.sum_eq_zero
    intro z hz
    rw [hmem'] at hz
    rw [Finset.sum_insertNone]
    exact fibre_zero hqw (coars_ndvd hW'q hz) (coars_ne_zero hW'ne hz)
  · intro y hy
    rw [hmem] at hy
    obtain ⟨g', y', rfl, hco, hy', hi⟩ := hii y hy
    rw [hi, Finset.mem_sigma]
    split_ifs at hco ⊢ with hg
    · exact ⟨(hmem' _).2 hco, by simp⟩
    · exact ⟨(hmem' _).2 hco, by simp⟩
  · rintro ⟨z, o⟩ hp
    rw [Finset.mem_sigma, hmem'] at hp
    rw [hmem]
    obtain ⟨hz, ho⟩ := hp
    cases o with
    | none => exact C2a hz
    | some v =>
      have hv : v ∈ z := by simpa using ho
      exact C2b hz hv
  · intro y hy
    rw [hmem] at hy
    obtain ⟨g', y', rfl, hco, hy', hi⟩ := hii y hy
    rw [hi]
    split_ifs with hg
    · subst hg; simp [jj]
    · simp [jj, mul_comm]
  · rintro ⟨z, o⟩ hp
    rw [Finset.mem_sigma, hmem'] at hp
    obtain ⟨hz, ho⟩ := hp
    have hzq := coars_ndvd hW'q hz
    cases o with
    | none =>
      simp only [jj, Option.elim]
      simp only [ii, tt_eq w z hqw hzq, filt_eq w z hqw hzq, if_true]
    | some v =>
      have hv : v ∈ z := by simpa using ho
      have hv1 : 1 < v := coars_gt hW'gt hz v hv
      have hzq' : ∀ b ∈ z.erase v, ¬ q ∣ b := fun b hb => hzq b (Multiset.mem_of_mem_erase hb)
      have hd : q ∣ v * w := dvd_mul_of_dvd_right hqw v
      simp only [jj, Option.elim]
      have hne : v * w ≠ w := by
        intro h; have : v * w > 1 * w := Nat.mul_lt_mul_of_pos_right hv1 (by omega)
        omega
      simp only [ii, tt_eq (v * w) (z.erase v) hd hzq', filt_eq (v * w) (z.erase v) hd hzq',
        if_neg hne, Nat.mul_div_cancel _ (by omega : 0 < w), Multiset.cons_erase hv]
  · intro y hy
    rw [hmem] at hy
    obtain ⟨g', y', rfl, hco, hy', hi⟩ := hii y hy
    simp only [hi]
    split_ifs with hg
    · subst hg; simp [jj]
    · simp [jj, mul_comm]

end FactMobL5

theorem factorization_coarsening_signed_orderings_sum_zero (q : ℕ) (hq : q.Prime)
    (W : Multiset ℕ) (hW : ∀ a ∈ W, 1 < a) (hdvd : q ∣ W.prod) (hsq : ¬ q ^ 2 ∣ W.prod)
    (hcard : 2 ≤ W.card) :
    ∑ᶠ (y : Multiset ℕ) (_ : IsFactorizationCoarsening W y),
      ((-1 : ℚ) ^ (y.card - 1) * ((y.card - 1).factorial : ℚ) /
        ∏ a ∈ (y.filter (fun a => ¬ q ∣ a)).toFinset,
          (((y.filter (fun a => ¬ q ∣ a)).count a).factorial : ℚ)) = 0 := by
  exact FactMobL5.lemma5 q hq W hW hdvd hsq hcard
