import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundy
import AFTD.Kb.GameTheoryEconomics.SlowExactNimMisere
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGeometricPaddedWitness
import AFTD.Kb.GameTheoryEconomics.FinsetMex
import AFTD.Kb.GameTheoryEconomics.SlowExactNimFollowers
import AFTD.Kb.GameTheoryEconomics.SlowExactNimMisereComp
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundyComp
import AFTD.Kb.GameTheoryEconomics.SlowExactNimStep

/-!
# op_2051_slow_exact_nim_joint_seven_witness

Topic: combinatorial_games   Node: bd0113fc11c5

Provenance: formalization of a published result. Source: arXiv:2611.14546; OP-2051

In slow exact k-Nim on k+2 piles, for every integer k ≥ 3, the geometric padded witness position slow_exact_nim_geometric_padded_witness 2 k has Sprague-Grundy value 7 and misère invariant 7.
-/

/-- number of piles of size vv -/
def op2051jw_cnt {nn : ℕ} (x : Fin nn → ℕ) (u : Fin 8) : ℕ :=
  (Finset.univ.filter (fun i => x i = u.val)).card

def op2051jw_skip (vv wv : ℕ) (u : Fin 8) : ℕ :=
  (if vv = u.val then 1 else 0) + (if wv = u.val then 1 else 0)

def op2051jw_shift (cv dv : Fin 8 → ℕ) (u : Fin 8) : ℕ :=
  (if hq : u.val + 1 < 8 then cv ⟨u.val + 1, hq⟩ - dv ⟨u.val + 1, hq⟩ else 0) + dv u

def op2051jw_legal (cv : Fin 8 → ℕ) (pp : Fin 8 × Fin 8) : Prop :=
  (∀ u : Fin 8, op2051jw_skip pp.1.val pp.2.val u ≤ cv u) ∧ cv 0 = op2051jw_skip pp.1.val pp.2.val 0

instance op2051jw_legal_dec (cv : Fin 8 → ℕ) : DecidablePred (op2051jw_legal cv) := by
  intro pp; unfold op2051jw_legal; infer_instance

def op2051jw_fol (s : (Fin 8 → ℕ) × ℕ) : Finset ((Fin 8 → ℕ) × ℕ) :=
  ((Finset.univ : Finset (Fin 8 × Fin 8)).filter (fun pp => op2051jw_legal s.1 pp)).image
    (fun pp => (op2051jw_shift s.1 (op2051jw_skip pp.1.val pp.2.val), s.2 - 1))

def op2051jw_gv (L : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ)) (s : (Fin 8 → ℕ) × ℕ) : ℕ :=
  ((L.find? (fun e => decide (e.1 = s))).map (fun e => e.2.1)).getD 0

def op2051jw_mv (L : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ)) (s : (Fin 8 → ℕ) × ℕ) : ℕ :=
  ((L.find? (fun e => decide (e.1 = s))).map (fun e => e.2.2)).getD 0

def op2051jw_good (s : (Fin 8 → ℕ) × ℕ) : Prop :=
  s.2 ≤ 7 ∧ (∀ u : Fin 8, u.val = s.2 → 1 ≤ s.2 → 2 ≤ s.1 u) ∧ (s.2 = 0 → 3 ≤ s.1 0)

def op2051jw_ok (L : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ)) (good : Bool) : Prop :=
  ∀ e ∈ L, (∀ s' ∈ op2051jw_fol e.1, s' ∈ L.map Prod.fst) ∧
    op2051jw_gv L e.1 = finset_mex ((op2051jw_fol e.1).image (op2051jw_gv L)) ∧
    op2051jw_mv L e.1 = (if (op2051jw_fol e.1).Nonempty then
        finset_mex ((op2051jw_fol e.1).image (op2051jw_mv L)) else 1) ∧
    (e.1.2 = 0 → op2051jw_fol e.1 = ∅) ∧ e.1.2 ≤ 7 ∧ (good = true → op2051jw_good e.1)

instance op2051jw_good_dec (s : (Fin 8 → ℕ) × ℕ) : Decidable (op2051jw_good s) := by
  unfold op2051jw_good; infer_instance

instance op2051jw_ok_dec (L) (gd) : Decidable (op2051jw_ok L gd) := by
  unfold op2051jw_ok; infer_instance


theorem op2051jw_pair_card {nn : ℕ} (x : Fin nn → ℕ) (ia ib : Fin nn) (hab : ia ≠ ib) (vv : ℕ) :
    (Finset.univ.filter (fun i => (i = ia ∨ i = ib) ∧ x i = vv)).card
      = (if x ia = vv then 1 else 0) + (if x ib = vv then 1 else 0) := by
  have : Finset.univ.filter (fun i => (i = ia ∨ i = ib) ∧ x i = vv)
      = ({ia, ib} : Finset (Fin nn)).filter (fun i => x i = vv) := by
    ext i; simp
  rw [this, Finset.filter_insert, Finset.filter_singleton]
  by_cases ha : x ia = vv <;> by_cases hb : x ib = vv <;> simp [ha, hb, hab]

theorem op2051jw_pair_le {nn : ℕ} (x : Fin nn → ℕ) (ia ib : Fin nn) (hab : ia ≠ ib) (vv : ℕ) :
    (if x ia = vv then 1 else 0) + (if x ib = vv then 1 else 0)
      ≤ (Finset.univ.filter (fun i => x i = vv)).card := by
  rw [← op2051jw_pair_card x ia ib hab vv]
  exact Finset.card_le_card (Finset.monotone_filter_right _ (fun i _ hq => hq.2))

theorem op2051jw_cnt_step {nn : ℕ} (x : Fin nn → ℕ) (hx : ∀ i, x i ≤ 7) (ia ib : Fin nn) (hab : ia ≠ ib)
    (hpos : ∀ i, i ≠ ia → i ≠ ib → 0 < x i) (u : Fin 8) :
    op2051jw_cnt (slow_exact_nim_step x ({ia, ib}ᶜ)) u
      = op2051jw_shift (op2051jw_cnt x) (op2051jw_skip (x ia) (x ib)) u := by
  have key : ∀ vv : ℕ,
      (Finset.univ.filter (fun i => slow_exact_nim_step x ({ia, ib}ᶜ) i = vv)).card
        + (Finset.univ.filter (fun i => (i = ia ∨ i = ib) ∧ x i = vv + 1)).card
      = (Finset.univ.filter (fun i => x i = vv + 1)).card
        + (Finset.univ.filter (fun i => (i = ia ∨ i = ib) ∧ x i = vv)).card := by
    intro vv
    simp only [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i = ia ∨ i = ib
    · have : i ∉ ({ia, ib} : Finset (Fin nn))ᶜ := by simp; tauto
      simp only [slow_exact_nim_step, this, if_false, hi, true_and]
      exact add_comm _ _
    · have : i ∈ ({ia, ib} : Finset (Fin nn))ᶜ := by simpa using hi
      have hp := hpos i (fun hq => hi (Or.inl hq)) (fun hq => hi (Or.inr hq))
      have e : (x i - 1 = vv) ↔ (x i = vv + 1) := by omega
      simp only [slow_exact_nim_step, this, if_true, hi, false_and, if_false, e]
  have k1 := key u.val
  rw [op2051jw_pair_card x ia ib hab, op2051jw_pair_card x ia ib hab] at k1
  have hle := op2051jw_pair_le x ia ib hab (u.val + 1)
  unfold op2051jw_cnt op2051jw_shift op2051jw_skip
  by_cases hq : u.val + 1 < 8
  · rw [dif_pos hq]
    show _ = ((Finset.univ.filter (fun i => x i = u.val + 1)).card
      - ((if x ia = u.val + 1 then 1 else 0) + (if x ib = u.val + 1 then 1 else 0))) + _
    omega
  · rw [dif_neg hq]
    have h0 : (Finset.univ.filter (fun i => x i = u.val + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; have := hx i; omega
    omega

def op2051jw_rel {nn : ℕ} (j : ℕ) (x : Fin nn → ℕ) (s : (Fin 8 → ℕ) × ℕ) : Prop :=
  (∀ i, x i ≤ 7) ∧ ∀ u : Fin 8, op2051jw_cnt x u = s.1 u + (if u.val = s.2 then j else 0)

theorem op2051jw_shift_embed (cv dv : Fin 8 → ℕ) (m j : ℕ) (hm1 : 1 ≤ m) (hm7 : m ≤ 7)
    (hdd : ∀ u : Fin 8, u.val = m → dv u ≤ cv u) (u : Fin 8) :
    op2051jw_shift (fun u => cv u + if u.val = m then j else 0) dv u
      = op2051jw_shift cv dv u + if u.val = m - 1 then j else 0 := by
  unfold op2051jw_shift
  by_cases hq : u.val + 1 < 8
  · rw [dif_pos hq, dif_pos hq]
    show (cv ⟨u.val + 1, hq⟩ + (if u.val + 1 = m then j else 0)) - dv ⟨u.val + 1, hq⟩ + dv u
      = (cv ⟨u.val + 1, hq⟩ - dv ⟨u.val + 1, hq⟩ + dv u) + (if u.val = m - 1 then j else 0)
    by_cases hu : u.val + 1 = m
    · have := hdd ⟨u.val + 1, hq⟩ hu
      rw [if_pos hu, if_pos (by omega)]; omega
    · rw [if_neg hu, if_neg (by omega)]; omega
  · rw [dif_neg hq, dif_neg hq]
    have : u.val ≠ m - 1 := by omega
    simp [this]

theorem op2051jw_rel_step {nn : ℕ} (j : ℕ) (x : Fin nn → ℕ) (s : (Fin 8 → ℕ) × ℕ)
    (hr : op2051jw_rel j x s) (ia ib : Fin nn) (hab : ia ≠ ib)
    (hpos : ∀ i, i ≠ ia → i ≠ ib → 0 < x i) (hm1 : 1 ≤ s.2) (hm7 : s.2 ≤ 7)
    (hdd : ∀ u : Fin 8, u.val = s.2 → op2051jw_skip (x ia) (x ib) u ≤ s.1 u) :
    op2051jw_rel j (slow_exact_nim_step x ({ia, ib}ᶜ))
      (op2051jw_shift s.1 (op2051jw_skip (x ia) (x ib)), s.2 - 1) := by
  refine ⟨fun i => ?_, fun u => ?_⟩
  · have := hr.1 i; unfold slow_exact_nim_step; split_ifs <;> omega
  · rw [op2051jw_cnt_step x hr.1 ia ib hab hpos u]
    have hc : op2051jw_cnt x = fun u => s.1 u + if u.val = s.2 then j else 0 := funext hr.2
    rw [hc, op2051jw_shift_embed _ _ _ _ hm1 hm7 hdd]


theorem op2051jw_skip_le_two (vv wv : ℕ) (u : Fin 8) : op2051jw_skip vv wv u ≤ 2 := by
  unfold op2051jw_skip; split_ifs <;> omega

theorem op2051jw_cnt_eq_skip {nn : ℕ} (x : Fin nn → ℕ) (ia ib : Fin nn) (hab : ia ≠ ib) (vv : ℕ)
    (hsub : ∀ i, x i = vv → i = ia ∨ i = ib) :
    (Finset.univ.filter (fun i => x i = vv)).card
      = (if x ia = vv then 1 else 0) + (if x ib = vv then 1 else 0) := by
  rw [← op2051jw_pair_card x ia ib hab vv]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hq; exact ⟨hsub i hq, hq⟩
  · intro hq; exact hq.2

theorem op2051jw_fol_snd (s s' : (Fin 8 → ℕ) × ℕ) (hq : s' ∈ op2051jw_fol s) : s'.2 = s.2 - 1 := by
  unfold op2051jw_fol at hq
  obtain ⟨pp, _, rfl⟩ := Finset.mem_image.1 hq
  rfl

theorem op2051jw_fwd (k j : ℕ) (x : Fin (k + 2) → ℕ) (s : (Fin 8 → ℕ) × ℕ)
    (hr : op2051jw_rel j x s) (hm0 : s.2 = 0 → op2051jw_fol s = ∅) (hm7 : s.2 ≤ 7)
    (hG : j = 0 ∨ op2051jw_good s) (y : Fin (k + 2) → ℕ)
    (hy : y ∈ slow_exact_nim_followers k (k + 2) x) :
    ∃ s' ∈ op2051jw_fol s, op2051jw_rel j y s' := by
  unfold slow_exact_nim_followers at hy
  obtain ⟨SS, hS, rfl⟩ := Finset.mem_image.1 hy
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
  have hc2 : SSᶜ.card = 2 := by
    rw [Finset.card_compl, Fintype.card_fin, hS.1.2]; omega
  obtain ⟨ia, ib, hab, hSab⟩ := Finset.card_eq_two.1 hc2
  have hS' : SS = ({ia, ib} : Finset (Fin (k + 2)))ᶜ := by rw [← hSab, compl_compl]
  subst hS'
  have hpos : ∀ i, i ≠ ia → i ≠ ib → 0 < x i := by
    intro i ha hb; apply hS.2; simp [ha, hb]
  have hxa := hr.1 ia
  have hxb := hr.1 ib
  have hcnt0 : op2051jw_cnt x 0 = op2051jw_skip (x ia) (x ib) 0 := by
    unfold op2051jw_cnt op2051jw_skip
    rw [op2051jw_cnt_eq_skip x ia ib hab]
    intro i hi
    by_contra hne; replace hne := not_or.1 hne
    have := hpos i hne.1 hne.2; simp at hi; omega
  have hle : ∀ u, op2051jw_skip (x ia) (x ib) u ≤ op2051jw_cnt x u := fun u =>
    op2051jw_pair_le x ia ib hab u.val
  have h0 := hr.2 0
  have hs0 := op2051jw_skip_le_two (x ia) (x ib) 0
  -- the move is legal in the abstract game
  have hlegal : op2051jw_legal s.1 (⟨x ia, by omega⟩, ⟨x ib, by omega⟩) := by
    refine ⟨fun u => ?_, ?_⟩
    · have h1 := hr.2 u
      have h2 := hle u
      have h3 := op2051jw_skip_le_two (x ia) (x ib) u
      show op2051jw_skip (x ia) (x ib) u ≤ s.1 u
      by_cases hu : u.val = s.2
      · rw [if_pos hu] at h1
        rcases hG with hj | hg
        · subst hj; omega
        · by_cases hm : 1 ≤ s.2
          · have := hg.2.1 u hu hm; omega
          · have h4 := hg.2.2 (by omega)
            have hu0 : u = 0 := Fin.ext (by simp; omega)
            subst hu0
            simp only [Fin.val_zero] at h0
            rw [if_pos (by omega)] at h0
            omega
      · rw [if_neg hu] at h1; omega
    · show s.1 0 = op2051jw_skip (x ia) (x ib) 0
      by_cases hu : (0 : Fin 8).val = s.2
      · rw [if_pos hu] at h0
        rcases hG with hj | hg
        · subst hj; omega
        · have h4 := hg.2.2 (by simp at hu; omega); omega
      · rw [if_neg hu] at h0; omega
  have hmem : (op2051jw_shift s.1 (op2051jw_skip (x ia) (x ib)), s.2 - 1) ∈ op2051jw_fol s := by
    unfold op2051jw_fol
    exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hlegal⟩, rfl⟩
  have hm1 : 1 ≤ s.2 := by
    by_contra hm
    have := hm0 (by omega)
    rw [this] at hmem; simp at hmem
  refine ⟨_, hmem, op2051jw_rel_step j x s hr ia ib hab hpos hm1 hm7 (fun u _ => hlegal.1 u)⟩

theorem op2051jw_bwd (k j : ℕ) (x : Fin (k + 2) → ℕ) (s : (Fin 8 → ℕ) × ℕ)
    (hr : op2051jw_rel j x s) (hm0 : s.2 = 0 → op2051jw_fol s = ∅) (hm7 : s.2 ≤ 7)
    (s' : (Fin 8 → ℕ) × ℕ) (hs' : s' ∈ op2051jw_fol s) :
    ∃ y ∈ slow_exact_nim_followers k (k + 2) x, op2051jw_rel j y s' := by
  have hm1 : 1 ≤ s.2 := by
    by_contra hm
    have := hm0 (by omega)
    rw [this] at hs'; simp at hs'
  unfold op2051jw_fol at hs'
  obtain ⟨pp, hp, rfl⟩ := Finset.mem_image.1 hs'
  have hp := (Finset.mem_filter.1 hp).2
  have hge : ∀ u, op2051jw_skip pp.1.val pp.2.val u ≤ op2051jw_cnt x u := by
    intro u; have := hr.2 u; have := hp.1 u; omega
  -- choose ia with x ia = pp.1
  have h1 := hge pp.1
  have hpos1 : 0 < (Finset.univ.filter (fun i => x i = pp.1.val)).card := by
    have : 1 ≤ op2051jw_skip pp.1.val pp.2.val pp.1 := by unfold op2051jw_skip; simp
    exact lt_of_lt_of_le this h1
  obtain ⟨ia, ha⟩ := Finset.card_pos.1 hpos1
  have ha : x ia = pp.1.val := (Finset.mem_filter.1 ha).2
  have hbex : ∃ ib, ib ≠ ia ∧ x ib = pp.2.val := by
    by_cases he : pp.1 = pp.2
    · have h2 := hge pp.2
      have : 2 ≤ (Finset.univ.filter (fun i => x i = pp.2.val)).card := by
        have : op2051jw_skip pp.1.val pp.2.val pp.2 = 2 := by unfold op2051jw_skip; simp [he]
        unfold op2051jw_cnt at h2; omega
      have hpos : 0 < ((Finset.univ.filter (fun i => x i = pp.2.val)).erase ia).card := by
        rw [Finset.card_erase_of_mem (by simp [ha, he])]; omega
      obtain ⟨ib, hb⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_erase, Finset.mem_filter] at hb
      exact ⟨ib, hb.1, hb.2.2⟩
    · have h2 := hge pp.2
      have : 0 < (Finset.univ.filter (fun i => x i = pp.2.val)).card := by
        have : 1 ≤ op2051jw_skip pp.1.val pp.2.val pp.2 := by unfold op2051jw_skip; simp
        unfold op2051jw_cnt at h2; omega
      obtain ⟨ib, hb⟩ := Finset.card_pos.1 this
      have hb : x ib = pp.2.val := (Finset.mem_filter.1 hb).2
      refine ⟨ib, ?_, hb⟩
      rintro rfl; exact he (Fin.ext (by omega))
  obtain ⟨ib, hba, hb⟩ := hbex
  have hab : ia ≠ ib := fun hq => hba hq.symm
  have hskip : op2051jw_skip (x ia) (x ib) = op2051jw_skip pp.1.val pp.2.val := by rw [ha, hb]
  -- positivity off {ia, ib}
  have hpos : ∀ i, i ≠ ia → i ≠ ib → 0 < x i := by
    intro i hia hib
    by_contra hz
    have hz : x i = 0 := by omega
    have hc0 : op2051jw_cnt x 0 = op2051jw_skip (x ia) (x ib) 0 := by
      have := hr.2 0
      rw [if_neg (by simp; omega)] at this
      rw [this, hskip]; exact hp.2
    have hsub : Finset.univ.filter (fun i => (i = ia ∨ i = ib) ∧ x i = 0)
        = Finset.univ.filter (fun i => x i = 0) := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.monotone_filter_right _ (fun i _ hq => hq.2)
      · rw [op2051jw_pair_card x ia ib hab]
        unfold op2051jw_cnt op2051jw_skip at hc0
        simp only [Fin.val_zero] at hc0
        omega
    have : i ∈ Finset.univ.filter (fun i => x i = 0) := by simp [hz]
    rw [← hsub] at this
    simp at this
    rcases this.1 with hq | hq
    · exact hia hq
    · exact hib hq
  refine ⟨slow_exact_nim_step x ({ia, ib}ᶜ), ?_, ?_⟩
  · unfold slow_exact_nim_followers
    refine Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]; omega
    · intro i hi; simp at hi; exact hpos i hi.1 hi.2
  · have := op2051jw_rel_step j x s hr ia ib hab hpos hm1 hm7
      (fun u _ => by rw [hskip]; exact hp.1 u)
    rw [hskip] at this
    exact this


theorem op2051jw_main (L : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ)) (gd : Bool) (hok : op2051jw_ok L gd)
    (k j : ℕ) (hj : j = 0 ∨ gd = true) :
    ∀ f (x : Fin (k + 2) → ℕ) (s : (Fin 8 → ℕ) × ℕ), s ∈ L.map Prod.fst →
      op2051jw_rel j x s → s.2 ≤ f →
      slow_exact_nim_grundy_comp k (k + 2) f x = op2051jw_gv L s ∧
      slow_exact_nim_misere_comp k (k + 2) f x = op2051jw_mv L s := by
  intro f
  induction f with
  | zero =>
    intro x s hs _ hf
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
    obtain ⟨_, hgv, hmv, hm0, _, _⟩ := hok e he
    have hf0 := hm0 (by omega)
    rw [hf0] at hgv hmv
    refine ⟨?_, ?_⟩
    · rw [hgv]; rfl
    · rw [hmv]; simp; rfl
  | succ f ih =>
    intro x s hs hr hf
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hcl, hgv, hmv, hm0, hm7, hgd⟩ := hok e he
    have hG : j = 0 ∨ op2051jw_good e.1 := by
      rcases hj with hq | hq
      · exact Or.inl hq
      · exact Or.inr (hgd hq)
    have hstep : ∀ y ∈ slow_exact_nim_followers k (k + 2) x,
        ∃ s' ∈ op2051jw_fol e.1,
          slow_exact_nim_grundy_comp k (k + 2) f y = op2051jw_gv L s' ∧
          slow_exact_nim_misere_comp k (k + 2) f y = op2051jw_mv L s' := by
      intro y hy
      obtain ⟨s', hs', hr'⟩ := op2051jw_fwd k j x e.1 hr hm0 hm7 hG y hy
      have h2 := op2051jw_fol_snd _ _ hs'
      exact ⟨s', hs', ih y s' (hcl s' hs') hr' (by omega)⟩
    have hstep' : ∀ s' ∈ op2051jw_fol e.1,
        ∃ y ∈ slow_exact_nim_followers k (k + 2) x,
          slow_exact_nim_grundy_comp k (k + 2) f y = op2051jw_gv L s' ∧
          slow_exact_nim_misere_comp k (k + 2) f y = op2051jw_mv L s' := by
      intro s' hs'
      obtain ⟨y, hy, hr'⟩ := op2051jw_bwd k j x e.1 hr hm0 hm7 s' hs'
      have h2 := op2051jw_fol_snd _ _ hs'
      exact ⟨y, hy, ih y s' (hcl s' hs') hr' (by omega)⟩
    have himg : (slow_exact_nim_followers k (k + 2) x).image (slow_exact_nim_grundy_comp k (k + 2) f)
        = (op2051jw_fol e.1).image (op2051jw_gv L) := by
      ext vv; simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨s', hs', h1, _⟩ := hstep y hy
        exact ⟨s', hs', h1.symm⟩
      · rintro ⟨s', hs', rfl⟩
        obtain ⟨y, hy, h1, _⟩ := hstep' s' hs'
        exact ⟨y, hy, h1⟩
    have himg' : (slow_exact_nim_followers k (k + 2) x).image (slow_exact_nim_misere_comp k (k + 2) f)
        = (op2051jw_fol e.1).image (op2051jw_mv L) := by
      ext vv; simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨s', hs', _, h1⟩ := hstep y hy
        exact ⟨s', hs', h1.symm⟩
      · rintro ⟨s', hs', rfl⟩
        obtain ⟨y, hy, _, h1⟩ := hstep' s' hs'
        exact ⟨y, hy, h1⟩
    have hne : (slow_exact_nim_followers k (k + 2) x).Nonempty ↔ (op2051jw_fol e.1).Nonempty := by
      rw [← Finset.image_nonempty (f := slow_exact_nim_grundy_comp k (k + 2) f), himg,
        Finset.image_nonempty]
    refine ⟨?_, ?_⟩
    · show finset_mex _ = _
      rw [himg, hgv]
    · show (if _ then _ else _) = _
      rw [hmv]
      by_cases hq : (op2051jw_fol e.1).Nonempty
      · rw [if_pos (hne.2 hq), if_pos hq, himg']
      · rw [if_neg (fun h' => hq (hne.1 h')), if_neg hq]

theorem op2051jw_wcnt (k : ℕ) (hk : 3 ≤ k) (u : Fin 8) :
    op2051jw_cnt (slow_exact_nim_geometric_padded_witness 2 k) u
      = (if u.val = 1 ∨ u.val = 2 ∨ u.val = 4 then 1 else 0) + (if u.val = 7 then k - 1 else 0) := by
  unfold op2051jw_cnt slow_exact_nim_geometric_padded_witness
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if (if i ≤ 2 then 2 ^ i else 2 ^ (2 + 1) - 1) = u.val
    then 1 else 0) (k + 2)]
  rw [show k + 2 = 3 + (k - 1) by omega, Finset.sum_range_add]
  have : ∀ x ∈ Finset.range (k - 1), (if (if 3 + x ≤ 2 then 2 ^ (3 + x) else 2 ^ (2 + 1) - 1) = u.val
      then 1 else 0) = (if 7 = u.val then 1 else 0) := by
    intro x _; rw [if_neg (show ¬ 3 + x ≤ 2 by omega)]; norm_num
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  fin_cases u <;> norm_num

theorem op2051jw_wrel (k K : ℕ) (hK : 3 ≤ K) (hKk : K ≤ k) :
    op2051jw_rel (k - K) (slow_exact_nim_geometric_padded_witness 2 k)
      (![0, 1, 1, 0, 1, 0, 0, K - 1], 7) := by
  refine ⟨fun i => ?_, fun u => ?_⟩
  · unfold slow_exact_nim_geometric_padded_witness
    split_ifs with hq
    · calc 2 ^ i.val ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hq
        _ ≤ 7 := by norm_num
    · norm_num
  · rw [op2051jw_wcnt k (by omega) u]
    fin_cases u <;> simp <;> omega

theorem op2051jw_wsum (k : ℕ) (hk : 3 ≤ k) :
    7 ≤ ∑ i, slow_exact_nim_geometric_padded_witness 2 k i := by
  have := Finset.single_le_sum (f := slow_exact_nim_geometric_padded_witness 2 k)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨3, by omega⟩ : Fin (k + 2)))
  unfold slow_exact_nim_geometric_padded_witness at this ⊢
  simpa using this

def op2051jw_table3 : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ) :=
  [((![0, 1, 1, 0, 1, 0, 0, 2], 7), 7, 7),
   ((![0, 1, 1, 1, 0, 0, 2, 0], 6), 6, 6),
   ((![0, 1, 2, 0, 0, 2, 0, 0], 5), 1, 1),
   ((![0, 2, 0, 0, 1, 0, 2, 0], 6), 4, 4),
   ((![0, 2, 0, 1, 0, 0, 1, 1], 6), 5, 5),
   ((![0, 2, 0, 1, 0, 2, 0, 0], 5), 5, 5),
   ((![0, 2, 1, 0, 0, 1, 1, 0], 5), 4, 4),
   ((![0, 2, 1, 0, 2, 0, 0, 0], 4), 4, 4),
   ((![0, 3, 0, 0, 1, 1, 0, 0], 4), 3, 3),
   ((![0, 3, 0, 2, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 0, 1, 0, 1, 0, 2, 0], 6), 0, 0),
   ((![1, 0, 1, 1, 0, 0, 1, 1], 6), 1, 1),
   ((![1, 0, 1, 1, 0, 2, 0, 0], 5), 1, 1),
   ((![1, 0, 2, 0, 0, 1, 1, 0], 5), 0, 0),
   ((![1, 0, 2, 0, 2, 0, 0, 0], 4), 0, 0),
   ((![1, 1, 0, 0, 1, 0, 1, 1], 6), 3, 3),
   ((![1, 1, 0, 0, 1, 2, 0, 0], 5), 3, 3),
   ((![1, 1, 0, 1, 0, 0, 0, 2], 6), 2, 2),
   ((![1, 1, 0, 1, 0, 1, 1, 0], 5), 2, 2),
   ((![1, 1, 0, 1, 2, 0, 0, 0], 4), 2, 2),
   ((![1, 1, 1, 0, 0, 0, 2, 0], 5), 3, 3),
   ((![1, 1, 1, 0, 0, 1, 0, 1], 5), 3, 3),
   ((![1, 1, 1, 0, 1, 1, 0, 0], 4), 3, 3),
   ((![1, 1, 1, 2, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 2, 0, 0, 0, 2, 0, 0], 4), 2, 2),
   ((![1, 2, 0, 0, 1, 0, 1, 0], 4), 2, 2),
   ((![1, 2, 0, 1, 1, 0, 0, 0], 3), 2, 2),
   ((![1, 2, 2, 0, 0, 0, 0, 0], 2), 2, 2),
   ((![2, 0, 0, 0, 1, 1, 1, 0], 5), 0, 1),
   ((![2, 0, 0, 0, 3, 0, 0, 0], 4), 0, 1),
   ((![2, 0, 0, 1, 0, 0, 2, 0], 5), 1, 0),
   ((![2, 0, 0, 1, 0, 1, 0, 1], 5), 1, 0),
   ((![2, 0, 0, 1, 1, 1, 0, 0], 4), 1, 0),
   ((![2, 0, 0, 3, 0, 0, 0, 0], 3), 1, 0),
   ((![2, 0, 1, 0, 0, 0, 1, 1], 5), 0, 1),
   ((![2, 0, 1, 0, 0, 2, 0, 0], 4), 0, 1),
   ((![2, 0, 1, 0, 1, 0, 1, 0], 4), 0, 1),
   ((![2, 0, 1, 1, 1, 0, 0, 0], 3), 0, 1),
   ((![2, 0, 3, 0, 0, 0, 0, 0], 2), 0, 1),
   ((![2, 1, 0, 0, 0, 1, 1, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 1, 0, 0, 1], 4), 1, 0),
   ((![2, 1, 0, 0, 2, 0, 0, 0], 3), 1, 0),
   ((![2, 1, 0, 1, 0, 1, 0, 0], 3), 1, 0),
   ((![2, 1, 1, 1, 0, 0, 0, 0], 2), 1, 0),
   ((![2, 3, 0, 0, 0, 0, 0, 0], 1), 1, 0),
   ((![3, 0, 0, 0, 1, 1, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 1, 0, 0, 1, 0], 3), 0, 1),
   ((![3, 0, 0, 2, 0, 0, 0, 0], 2), 0, 1),
   ((![3, 0, 1, 0, 1, 0, 0, 0], 2), 0, 1),
   ((![3, 1, 1, 0, 0, 0, 0, 0], 1), 0, 1),
   ((![5, 0, 0, 0, 0, 0, 0, 0], 0), 0, 1)]

def op2051jw_table4 : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ) :=
  [((![0, 1, 1, 0, 1, 0, 0, 3], 7), 7, 7),
   ((![0, 1, 1, 1, 0, 0, 3, 0], 6), 6, 6),
   ((![0, 1, 2, 0, 0, 3, 0, 0], 5), 1, 1),
   ((![0, 2, 0, 0, 1, 0, 3, 0], 6), 4, 4),
   ((![0, 2, 0, 1, 0, 0, 2, 1], 6), 5, 5),
   ((![0, 2, 0, 1, 0, 3, 0, 0], 5), 5, 5),
   ((![0, 2, 1, 0, 0, 2, 1, 0], 5), 4, 4),
   ((![0, 2, 1, 0, 3, 0, 0, 0], 4), 4, 4),
   ((![0, 3, 0, 0, 2, 1, 0, 0], 4), 3, 3),
   ((![0, 3, 0, 3, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 0, 1, 0, 1, 0, 3, 0], 6), 0, 0),
   ((![1, 0, 1, 1, 0, 0, 2, 1], 6), 1, 1),
   ((![1, 0, 1, 1, 0, 3, 0, 0], 5), 1, 1),
   ((![1, 0, 2, 0, 0, 2, 1, 0], 5), 0, 0),
   ((![1, 0, 2, 0, 3, 0, 0, 0], 4), 0, 0),
   ((![1, 1, 0, 0, 1, 0, 2, 1], 6), 3, 3),
   ((![1, 1, 0, 0, 1, 3, 0, 0], 5), 3, 3),
   ((![1, 1, 0, 1, 0, 0, 1, 2], 6), 2, 2),
   ((![1, 1, 0, 1, 0, 2, 1, 0], 5), 2, 2),
   ((![1, 1, 0, 1, 3, 0, 0, 0], 4), 2, 2),
   ((![1, 1, 1, 0, 0, 1, 2, 0], 5), 3, 3),
   ((![1, 1, 1, 0, 0, 2, 0, 1], 5), 3, 3),
   ((![1, 1, 1, 0, 2, 1, 0, 0], 4), 3, 3),
   ((![1, 1, 1, 3, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 2, 0, 0, 1, 2, 0, 0], 4), 2, 2),
   ((![1, 2, 0, 0, 2, 0, 1, 0], 4), 2, 2),
   ((![1, 2, 0, 2, 1, 0, 0, 0], 3), 2, 2),
   ((![1, 2, 3, 0, 0, 0, 0, 0], 2), 2, 2),
   ((![2, 0, 0, 0, 1, 2, 1, 0], 5), 0, 1),
   ((![2, 0, 0, 0, 4, 0, 0, 0], 4), 0, 1),
   ((![2, 0, 0, 1, 0, 1, 2, 0], 5), 1, 0),
   ((![2, 0, 0, 1, 0, 2, 0, 1], 5), 1, 0),
   ((![2, 0, 0, 1, 2, 1, 0, 0], 4), 1, 0),
   ((![2, 0, 0, 4, 0, 0, 0, 0], 3), 1, 0),
   ((![2, 0, 1, 0, 0, 0, 3, 0], 5), 0, 1),
   ((![2, 0, 1, 0, 0, 1, 1, 1], 5), 0, 1),
   ((![2, 0, 1, 0, 1, 2, 0, 0], 4), 0, 1),
   ((![2, 0, 1, 0, 2, 0, 1, 0], 4), 0, 1),
   ((![2, 0, 1, 2, 1, 0, 0, 0], 3), 0, 1),
   ((![2, 0, 4, 0, 0, 0, 0, 0], 2), 0, 1),
   ((![2, 1, 0, 0, 0, 3, 0, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 1, 1, 1, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 2, 0, 0, 1], 4), 1, 0),
   ((![2, 1, 0, 1, 2, 0, 0, 0], 3), 1, 0),
   ((![2, 1, 0, 2, 0, 1, 0, 0], 3), 1, 0),
   ((![2, 1, 2, 1, 0, 0, 0, 0], 2), 1, 0),
   ((![2, 4, 0, 0, 0, 0, 0, 0], 1), 1, 0),
   ((![3, 0, 0, 0, 3, 0, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 1, 1, 1, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 2, 0, 0, 1, 0], 3), 0, 1),
   ((![3, 0, 1, 2, 0, 0, 0, 0], 2), 0, 1),
   ((![3, 0, 2, 0, 1, 0, 0, 0], 2), 0, 1),
   ((![3, 2, 1, 0, 0, 0, 0, 0], 1), 0, 1),
   ((![6, 0, 0, 0, 0, 0, 0, 0], 0), 0, 1)]

def op2051jw_table5 : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ) :=
  [((![0, 1, 1, 0, 1, 0, 0, 4], 7), 7, 7),
   ((![0, 1, 1, 1, 0, 0, 4, 0], 6), 6, 6),
   ((![0, 1, 2, 0, 0, 4, 0, 0], 5), 1, 1),
   ((![0, 2, 0, 0, 1, 0, 4, 0], 6), 4, 4),
   ((![0, 2, 0, 1, 0, 0, 3, 1], 6), 5, 5),
   ((![0, 2, 0, 1, 0, 4, 0, 0], 5), 5, 5),
   ((![0, 2, 1, 0, 0, 3, 1, 0], 5), 4, 4),
   ((![0, 2, 1, 0, 4, 0, 0, 0], 4), 4, 4),
   ((![0, 3, 0, 0, 3, 1, 0, 0], 4), 3, 3),
   ((![0, 3, 0, 4, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 0, 1, 0, 1, 0, 4, 0], 6), 0, 0),
   ((![1, 0, 1, 1, 0, 0, 3, 1], 6), 1, 1),
   ((![1, 0, 1, 1, 0, 4, 0, 0], 5), 1, 1),
   ((![1, 0, 2, 0, 0, 3, 1, 0], 5), 0, 0),
   ((![1, 0, 2, 0, 4, 0, 0, 0], 4), 0, 0),
   ((![1, 1, 0, 0, 1, 0, 3, 1], 6), 3, 3),
   ((![1, 1, 0, 0, 1, 4, 0, 0], 5), 3, 3),
   ((![1, 1, 0, 1, 0, 0, 2, 2], 6), 2, 2),
   ((![1, 1, 0, 1, 0, 3, 1, 0], 5), 2, 2),
   ((![1, 1, 0, 1, 4, 0, 0, 0], 4), 2, 2),
   ((![1, 1, 1, 0, 0, 2, 2, 0], 5), 3, 3),
   ((![1, 1, 1, 0, 0, 3, 0, 1], 5), 3, 3),
   ((![1, 1, 1, 0, 3, 1, 0, 0], 4), 3, 3),
   ((![1, 1, 1, 4, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 2, 0, 0, 2, 2, 0, 0], 4), 2, 2),
   ((![1, 2, 0, 0, 3, 0, 1, 0], 4), 2, 2),
   ((![1, 2, 0, 3, 1, 0, 0, 0], 3), 2, 2),
   ((![1, 2, 4, 0, 0, 0, 0, 0], 2), 2, 2),
   ((![2, 0, 0, 0, 1, 3, 1, 0], 5), 0, 1),
   ((![2, 0, 0, 0, 5, 0, 0, 0], 4), 0, 1),
   ((![2, 0, 0, 1, 0, 2, 2, 0], 5), 1, 0),
   ((![2, 0, 0, 1, 0, 3, 0, 1], 5), 1, 0),
   ((![2, 0, 0, 1, 3, 1, 0, 0], 4), 1, 0),
   ((![2, 0, 0, 5, 0, 0, 0, 0], 3), 1, 0),
   ((![2, 0, 1, 0, 0, 1, 3, 0], 5), 0, 1),
   ((![2, 0, 1, 0, 0, 2, 1, 1], 5), 0, 1),
   ((![2, 0, 1, 0, 2, 2, 0, 0], 4), 0, 1),
   ((![2, 0, 1, 0, 3, 0, 1, 0], 4), 0, 1),
   ((![2, 0, 1, 3, 1, 0, 0, 0], 3), 0, 1),
   ((![2, 0, 5, 0, 0, 0, 0, 0], 2), 0, 1),
   ((![2, 1, 0, 0, 1, 3, 0, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 2, 1, 1, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 3, 0, 0, 1], 4), 1, 0),
   ((![2, 1, 0, 2, 2, 0, 0, 0], 3), 1, 0),
   ((![2, 1, 0, 3, 0, 1, 0, 0], 3), 1, 0),
   ((![2, 1, 3, 1, 0, 0, 0, 0], 2), 1, 0),
   ((![2, 5, 0, 0, 0, 0, 0, 0], 1), 1, 0),
   ((![3, 0, 0, 1, 3, 0, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 2, 1, 1, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 3, 0, 0, 1, 0], 3), 0, 1),
   ((![3, 0, 2, 2, 0, 0, 0, 0], 2), 0, 1),
   ((![3, 0, 3, 0, 1, 0, 0, 0], 2), 0, 1),
   ((![3, 3, 1, 0, 0, 0, 0, 0], 1), 0, 1),
   ((![7, 0, 0, 0, 0, 0, 0, 0], 0), 0, 1)]

def op2051jw_table6 : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ) :=
  [((![0, 1, 1, 0, 1, 0, 0, 5], 7), 7, 7),
   ((![0, 1, 1, 1, 0, 0, 5, 0], 6), 6, 6),
   ((![0, 1, 2, 0, 0, 5, 0, 0], 5), 1, 1),
   ((![0, 2, 0, 0, 1, 0, 5, 0], 6), 4, 4),
   ((![0, 2, 0, 1, 0, 0, 4, 1], 6), 5, 5),
   ((![0, 2, 0, 1, 0, 5, 0, 0], 5), 5, 5),
   ((![0, 2, 1, 0, 0, 4, 1, 0], 5), 4, 4),
   ((![0, 2, 1, 0, 5, 0, 0, 0], 4), 4, 4),
   ((![0, 3, 0, 0, 4, 1, 0, 0], 4), 3, 3),
   ((![0, 3, 0, 5, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 0, 1, 0, 1, 0, 5, 0], 6), 0, 0),
   ((![1, 0, 1, 1, 0, 0, 4, 1], 6), 1, 1),
   ((![1, 0, 1, 1, 0, 5, 0, 0], 5), 1, 1),
   ((![1, 0, 2, 0, 0, 4, 1, 0], 5), 0, 0),
   ((![1, 0, 2, 0, 5, 0, 0, 0], 4), 0, 0),
   ((![1, 1, 0, 0, 1, 0, 4, 1], 6), 3, 3),
   ((![1, 1, 0, 0, 1, 5, 0, 0], 5), 3, 3),
   ((![1, 1, 0, 1, 0, 0, 3, 2], 6), 2, 2),
   ((![1, 1, 0, 1, 0, 4, 1, 0], 5), 2, 2),
   ((![1, 1, 0, 1, 5, 0, 0, 0], 4), 2, 2),
   ((![1, 1, 1, 0, 0, 3, 2, 0], 5), 3, 3),
   ((![1, 1, 1, 0, 0, 4, 0, 1], 5), 3, 3),
   ((![1, 1, 1, 0, 4, 1, 0, 0], 4), 3, 3),
   ((![1, 1, 1, 5, 0, 0, 0, 0], 3), 3, 3),
   ((![1, 2, 0, 0, 3, 2, 0, 0], 4), 2, 2),
   ((![1, 2, 0, 0, 4, 0, 1, 0], 4), 2, 2),
   ((![1, 2, 0, 4, 1, 0, 0, 0], 3), 2, 2),
   ((![1, 2, 5, 0, 0, 0, 0, 0], 2), 2, 2),
   ((![2, 0, 0, 0, 1, 4, 1, 0], 5), 0, 1),
   ((![2, 0, 0, 0, 6, 0, 0, 0], 4), 0, 1),
   ((![2, 0, 0, 1, 0, 3, 2, 0], 5), 1, 0),
   ((![2, 0, 0, 1, 0, 4, 0, 1], 5), 1, 0),
   ((![2, 0, 0, 1, 4, 1, 0, 0], 4), 1, 0),
   ((![2, 0, 0, 6, 0, 0, 0, 0], 3), 1, 0),
   ((![2, 0, 1, 0, 0, 2, 3, 0], 5), 0, 1),
   ((![2, 0, 1, 0, 0, 3, 1, 1], 5), 0, 1),
   ((![2, 0, 1, 0, 3, 2, 0, 0], 4), 0, 1),
   ((![2, 0, 1, 0, 4, 0, 1, 0], 4), 0, 1),
   ((![2, 0, 1, 4, 1, 0, 0, 0], 3), 0, 1),
   ((![2, 0, 6, 0, 0, 0, 0, 0], 2), 0, 1),
   ((![2, 1, 0, 0, 2, 3, 0, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 3, 1, 1, 0], 4), 1, 0),
   ((![2, 1, 0, 0, 4, 0, 0, 1], 4), 1, 0),
   ((![2, 1, 0, 3, 2, 0, 0, 0], 3), 1, 0),
   ((![2, 1, 0, 4, 0, 1, 0, 0], 3), 1, 0),
   ((![2, 1, 4, 1, 0, 0, 0, 0], 2), 1, 0),
   ((![2, 6, 0, 0, 0, 0, 0, 0], 1), 1, 0),
   ((![3, 0, 0, 2, 3, 0, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 3, 1, 1, 0, 0], 3), 0, 1),
   ((![3, 0, 0, 4, 0, 0, 1, 0], 3), 0, 1),
   ((![3, 0, 3, 2, 0, 0, 0, 0], 2), 0, 1),
   ((![3, 0, 4, 0, 1, 0, 0, 0], 2), 0, 1),
   ((![3, 4, 1, 0, 0, 0, 0, 0], 1), 0, 1),
   ((![8, 0, 0, 0, 0, 0, 0, 0], 0), 0, 1)]


set_option maxRecDepth 100000 in
theorem op2051jw_ok3 : op2051jw_ok op2051jw_table3 false := by decide +kernel

set_option maxRecDepth 100000 in
theorem op2051jw_ok4 : op2051jw_ok op2051jw_table4 false := by decide +kernel

set_option maxRecDepth 100000 in
theorem op2051jw_ok5 : op2051jw_ok op2051jw_table5 false := by decide +kernel

set_option maxRecDepth 100000 in
theorem op2051jw_ok6 : op2051jw_ok op2051jw_table6 true := by decide +kernel

theorem op2051jw_apply (L : List (((Fin 8 → ℕ) × ℕ) × ℕ × ℕ)) (gd : Bool) (hok : op2051jw_ok L gd)
    (k K : ℕ) (hK : 3 ≤ K) (hKk : K ≤ k) (hj : k - K = 0 ∨ gd = true)
    (hs : ((![0, 1, 1, 0, 1, 0, 0, K - 1], 7) : (Fin 8 → ℕ) × ℕ) ∈ L.map Prod.fst)
    (hv : op2051jw_gv L (![0, 1, 1, 0, 1, 0, 0, K - 1], 7) = 7 ∧
      op2051jw_mv L (![0, 1, 1, 0, 1, 0, 0, K - 1], 7) = 7) :
    slow_exact_nim_grundy k (k + 2) (slow_exact_nim_geometric_padded_witness 2 k) = 7 ∧
    slow_exact_nim_misere k (k + 2) (slow_exact_nim_geometric_padded_witness 2 k) = 7 := by
  have hq := op2051jw_main L gd hok k (k - K) hj _ _ _ hs (op2051jw_wrel k K hK hKk)
    (op2051jw_wsum k (by omega))
  unfold slow_exact_nim_grundy slow_exact_nim_misere
  rw [hq.1, hq.2]; exact hv

/-- The geometric padded witness position achieves Sprague-Grundy value 7 and misère invariant 7 in slow exact k-Nim on k+2 piles for all k ≥ 3. -/
theorem op_2051_slow_exact_nim_joint_seven_witness (k : ℕ) (hk : 3 ≤ k) :
    slow_exact_nim_grundy k (k + 2) (slow_exact_nim_geometric_padded_witness 2 k) = 7 ∧
    slow_exact_nim_misere k (k + 2) (slow_exact_nim_geometric_padded_witness 2 k) = 7 := by
  by_cases h6 : 6 ≤ k
  · exact op2051jw_apply _ true op2051jw_ok6 k 6 (by norm_num) h6 (Or.inr rfl) (by decide)
      (by decide)
  · interval_cases k
    · exact op2051jw_apply _ false op2051jw_ok3 3 3 le_rfl le_rfl (Or.inl rfl) (by decide)
        (by decide)
    · exact op2051jw_apply _ false op2051jw_ok4 4 4 (by norm_num) le_rfl (Or.inl rfl) (by decide)
        (by decide)
    · exact op2051jw_apply _ false op2051jw_ok5 5 5 (by norm_num) le_rfl (Or.inl rfl) (by decide)
        (by decide)
