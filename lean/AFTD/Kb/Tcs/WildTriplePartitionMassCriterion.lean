import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.CanonicalPermutationAvoidanceOfLocalLemma
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfBlockCutCondition
import AFTD.Kb.Tcs.FiniteProductOneSubLowerBoundByFibres
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.G

/-!
# wild_triple_partition_mass_criterion

Topic: graphs   Node: 93e96f36e485

Provenance: helper lemma. Uniform version of the permutation-event proof for OP-306 / arXiv:2610.22142, Section 6; builds on the proved n=279 case. Arithmetic hypotheses are explicit, not assumed true for all q.

For an odd number q of triple blocks, q>=3, a proper edge coloring of K_(3q) with 3q colors and a bijection between colors and their unique missing vertices has wild number at most 2q if the displayed positional and vertex canonical seal-event sums, using weight (21/20)^d/(3q)_d, are each at most 1/50.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {q : ℕ}
def wtc_blk (v : Fin (3 * q)) : Fin q := ⟨v.val / 3, by omega⟩

def wtc_pos (T : Finset (Fin q)) : Finset (Fin (3 * q)) :=
  Finset.univ.filter fun v => wtc_blk  v ∈ T

theorem wtc_mem_pos {v : Fin (3 * q)} {T : Finset (Fin q)} : v ∈ wtc_pos  T ↔ wtc_blk  v ∈ T := by
  simp [wtc_pos ]

theorem wtc_blk_fibre (b : Fin q) :
    (Finset.univ.filter fun v : Fin (3 * q) => wtc_blk  v = b).card = 3 := by
  have hb := b.isLt
  have : (Finset.univ.filter fun v : Fin (3 * q) => wtc_blk  v = b) =
      {⟨3 * b.val, by omega⟩, ⟨3 * b.val + 1, by omega⟩, ⟨3 * b.val + 2, by omega⟩} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, wtc_blk , Fin.ext_iff]
    omega
  rw [this, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_pair (by simp [Fin.ext_iff])]

theorem wtc_card_pos (T : Finset (Fin q)) : (wtc_pos  T).card = 3 * T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := wtc_blk ) (t := T)]
  · rw [Finset.sum_congr rfl (g := fun _ => 3), Finset.sum_const, smul_eq_mul, mul_comm]
    intro b hb
    conv_rhs => rw [← wtc_blk_fibre b]
    have : (wtc_pos  T).filter (fun v => wtc_blk  v = b) = Finset.univ.filter (fun v => wtc_blk  v = b) := by
      ext v
      rw [Finset.mem_filter, Finset.mem_filter, wtc_mem_pos ]
      constructor
      · exact fun h => ⟨Finset.mem_univ _, h.2⟩
      · intro h; exact ⟨h.2 ▸ hb, h.2⟩
    rw [this]
  · intro v hv
    exact wtc_mem_pos.1 hv

noncomputable def wtc_wt (d : ℕ) : ℝ := (21 / 20 : ℝ) ^ d / ((Nat.descFactorial (3 * q) d : ℕ) : ℝ)

theorem wtc_wt_nonneg (d : ℕ) : 0 ≤ wtc_wt (q := q)  d := by
  unfold wtc_wt ; positivity

theorem wtc_wt_lt_one (hq : 3 ≤ q) (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ (3 * (q / 2))) : wtc_wt (q := q)  d < 1 := by
  unfold wtc_wt 
  have hdesc : (2 : ℕ) ^ d ≤ Nat.descFactorial (3 * q) d :=
    le_trans (Nat.pow_le_pow_left (by omega) d) (Nat.pow_sub_le_descFactorial (3 * q) d)
  have hpos : (0 : ℝ) < ((Nat.descFactorial (3 * q) d : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 (by omega)
  rw [div_lt_one hpos]
  calc (21 / 20 : ℝ) ^ d < (2 : ℝ) ^ d := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    _ ≤ _ := by exact_mod_cast hdesc

open Classical in
@[irreducible] noncomputable def wtc_E (c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin (3 * q))) :
    Finset (Fin (3 * q) × Finset (Fin q) × (Fin (3 * q) → Fin (3 * q))) :=
  Finset.univ.filter fun t => 1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧
    (∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧
    w279_closed c t.1 ((wtc_pos  t.2.1).image t.2.2)

theorem wtc_mem_filter_univ {α : Type*} {fi : Fintype α} {P : α → Prop} {inst : DecidablePred P} {a : α} :
    a ∈ @Finset.filter α P inst (@Finset.univ α fi) ↔ P a :=
  ⟨fun h => ((@Finset.mem_filter α P inst _ a).1 h).2,
    fun h => (@Finset.mem_filter α P inst _ a).2 ⟨@Finset.mem_univ α fi a, h⟩⟩

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem wtc_mem_E {c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin (3 * q))}
    {t : Fin (3 * q) × Finset (Fin q) × (Fin (3 * q) → Fin (3 * q))} :
    t ∈ wtc_E c ↔ 1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧
      (∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧
      w279_closed c t.1 ((wtc_pos  t.2.1).image t.2.2) := by
  unfold wtc_E 
  exact wtc_mem_filter_univ 

section
variable (hodd : q % 2 = 1)
variable (c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin (3 * q))) (m : Fin (3 * q) ≃ Fin (3 * q))
  (hm : ∀ (i : Fin (3 * q)) (v : Fin (3 * q)), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
include hm hodd

theorem wtc_R_card (i : Fin (3 * q)) : (w279_R c m i).card = (3 * q / 2) := by
  have := w279_card_R c m hm i
  omega

set_option maxRecDepth 100000 in
/-- the events of colour `i` on blocks `T` -/
theorem wtc_fibre_card (i : Fin (3 * q)) (T : Finset (Fin q)) (P : Finset (Fin (3 * q)) → Prop) [DecidablePred P]
    (Fsel : Finset (Fin (3 * q) × Finset (Fin q) × (Fin (3 * q) → Fin (3 * q))))
    (hF : ∀ t ∈ Fsel, t.1 = i → t.2.1 = T → (∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧
      P ((wtc_pos  t.2.1).image t.2.2)) :
    (Fsel.filter fun t => (t.1, t.2.1) = (i, T)).card ≤ (3 * T.card).factorial *
      (Finset.univ.filter fun U : Finset (Fin (3 * q)) => U.card = 3 * T.card ∧ P U).card := by
  classical
  rw [← wtc_card_pos ]
  refine le_trans ?_ (w279_count_events (wtc_pos  T) P)
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht
    obtain ⟨ht, h1, h2⟩ := ht
    obtain ⟨g1, g2, g3⟩ := hF t ht h1 h2
    rw [h2] at g1 g2 g3
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨g1, g2, g3⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht ht'
    obtain ⟨-, h1, h2⟩ := ht
    obtain ⟨-, h1', h2'⟩ := ht'
    exact Prod.ext (h1.trans h1'.symm) (Prod.ext (h2.trans h2'.symm) h)

set_option maxRecDepth 100000 in
theorem wtc_pos_mass (hpos : (∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ q / 2 then (3 * q : ℝ) * (((3 * (m + 1)).factorial * Nat.choose (3 * q / 2) (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0) ≤ 1 / 50)) (p : Fin (3 * q)) :
    ∑ t ∈ (wtc_E c).filter (fun t => p ∈ wtc_pos  t.2.1), wtc_wt (q := q) (wtc_pos  t.2.1).card ≤ 1 / 50 := by
  classical
  set Fsel := (wtc_E c).filter (fun t => p ∈ wtc_pos  t.2.1) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧ wtc_blk  p ∈ t.2.1) ∧
      ((∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧
      w279_closed c t.1 ((wtc_pos  t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, wtc_mem_E ] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1, wtc_mem_pos.1 ht.2⟩, ht.1.2.2⟩
  let 𝒯 : Finset (Finset (Fin q)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ (q / 2) ∧ wtc_blk  p ∈ T
  let φ : ℕ → ℝ := fun h => (((3 * h).factorial * Nat.choose (3 * q / 2) (3 * h / 2) : ℕ) : ℝ) * wtc_wt (q := q) (3 * h)
  have step1 : ∑ t ∈ Fsel, wtc_wt (q := q) (wtc_pos  t.2.1).card ≤ ∑ x ∈ (Finset.univ : Finset (Fin (3 * q))) ×ˢ 𝒯, φ x.2.card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), wtc_wt (q := q) (wtc_pos  t.2.1).card = wtc_wt (q := q) (3 * x.2.card) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [wtc_card_pos , ← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := wtc_fibre_card hodd c m hm x.1 x.2 (fun U => w279_closed c x.1 U) Fsel ?_
      · have hc2 := w279_count_closed c m hm x.1 (3 * x.2.card)
        rw [wtc_R_card hodd c m hm] at hc2
        have hc3 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (3 * x.2.card).factorial * Nat.choose (3 * q / 2) (3 * x.2.card / 2) := by
          refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
          intro U hU
          simp only [Finset.mem_filter] at hU ⊢
          exact hU
        simp only [φ]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc3) (wtc_wt_nonneg  _)
      · intro t ht hi _
        obtain ⟨-, h1, h2, h3⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin (3 * q))) ×ˢ 𝒯, φ x.2.card = (3 * q) * ∑ T ∈ 𝒯, φ T.card := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_cast
  have step3 : ∑ T ∈ 𝒯, φ T.card = ∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ (q / 2) then φ (m + 1) else 0) := by
    set b := wtc_blk  p
    have hcard : (Finset.univ.erase b).card = (q - 1) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have e1 : ∑ T ∈ 𝒯, φ T.card = ∑ T' ∈ (Finset.univ.erase b).powerset.filter (fun T' => T'.card + 1 ≤ (q / 2)),
        φ (T'.card + 1) := by
      refine Finset.sum_nbij' (fun T => T.erase b) (fun T' => insert b T') ?_ ?_ ?_ ?_ ?_
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_add_one hT.2.2]; exact hT.2.1
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.card_insert_of_notMem hb]
        exact ⟨by omega, hT'.2, Finset.mem_insert_self _ _⟩
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        exact Finset.insert_erase hT.2.2
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        exact Finset.erase_insert hb
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        rw [Finset.card_erase_add_one hT.2.2]
    rw [e1, Finset.sum_filter]
    have := Finset.sum_powerset_apply_card (fun m => if m + 1 ≤ (q / 2) then φ (m + 1) else 0)
      (x := Finset.univ.erase b)
    rw [hcard, Nat.sub_add_cancel (by have := p.isLt; omega : 1 ≤ q)] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := by rw [step2, step3]
    _ = ∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ (q / 2) then ((3 * q) : ℝ) * (((3 * (m + 1)).factorial * Nat.choose (3 * q / 2) (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs
      · simp only [φ]; ring
      · ring
    _ ≤ 1 / 50 := hpos

set_option maxRecDepth 100000 in
theorem wtc_vert_mass (hvert : (∑ m ∈ Finset.range (q + 1), ((Nat.choose q m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ q / 2 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) ≤ 1 / 50)) (w : Fin (3 * q)) :
    ∑ t ∈ (wtc_E c).filter (fun t => w ∈ (wtc_pos  t.2.1).image t.2.2),
      wtc_wt (q := q) (wtc_pos  t.2.1).card ≤ 1 / 50 := by
  classical
  set Fsel := (wtc_E c).filter (fun t => w ∈ (wtc_pos  t.2.1).image t.2.2) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2)) ∧
      ((∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧
      (w279_closed c t.1 ((wtc_pos  t.2.1).image t.2.2) ∧ w ∈ (wtc_pos  t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, wtc_mem_E ] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1⟩, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2, ht.2⟩
  let 𝒯 : Finset (Finset (Fin q)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ (q / 2)
  let X : ℕ → ℕ := fun s => if s % 2 = 1 then Nat.choose (3 * q / 2) (s / 2) else 0
  let Y : ℕ → ℕ := fun s => Nat.choose (3 * q / 2 - 1) (s / 2 - 1)
  let bnd : Fin (3 * q) → ℕ → ℝ := fun i s => (s.factorial : ℝ) * (if m i = w then (X s : ℝ) else (Y s : ℝ))
  have step1 : ∑ t ∈ Fsel, wtc_wt (q := q) (wtc_pos  t.2.1).card ≤
      ∑ x ∈ (Finset.univ : Finset (Fin (3 * q))) ×ˢ 𝒯, bnd x.1 (3 * x.2.card) * wtc_wt (q := q) (3 * x.2.card) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), wtc_wt (q := q) (wtc_pos  t.2.1).card = wtc_wt (q := q) (3 * x.2.card) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [wtc_card_pos , ← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := wtc_fibre_card hodd c m hm x.1 x.2 (fun U => w279_closed c x.1 U ∧ w ∈ U) Fsel ?_
      · have hc2 : (Finset.univ.filter fun U : Finset (Fin (3 * q)) => U.card = 3 * x.2.card ∧
            (w279_closed c x.1 U ∧ w ∈ U)).card ≤ if m x.1 = w then X (3 * x.2.card) else Y (3 * x.2.card) := by
          split_ifs with hmw
          · have := w279_count_closed_mem_m c m hm x.1 (3 * x.2.card)
            rw [wtc_R_card hodd c m hm, hmw] at this
            exact this
          · have := w279_count_closed_mem c m hm x.1 (3 * x.2.card) w (Ne.symm hmw)
            rw [wtc_R_card hodd c m hm] at this
            exact this
        have hc3 : ((Fsel.filter fun t => (t.1, t.2.1) = x).card : ℝ) ≤ bnd x.1 (3 * x.2.card) := by
          have h4 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (3 * x.2.card).factorial *
              (if m x.1 = w then X (3 * x.2.card) else Y (3 * x.2.card)) := by
            refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
            intro U hU
            simp only [Finset.mem_filter] at hU ⊢
            exact hU
          simp only [bnd]
          split_ifs at h4 ⊢ <;> exact_mod_cast h4
        exact mul_le_mul_of_nonneg_right hc3 (wtc_wt_nonneg  _)
      · intro t ht hi _
        obtain ⟨-, h1, h2, h3, h4⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3, h4⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hsumcol : ∀ s, ∑ i : Fin (3 * q), bnd i s = (((s.factorial * X s + (3 * q - 1) * (s.factorial * Y s)) : ℕ) : ℝ) := by
    intro s
    have h1 : (Finset.univ.filter fun i : Fin (3 * q) => m i = w) = {m.symm w} := by
      ext i; simp [Equiv.apply_eq_iff_eq_symm_apply]
    have h2 : (Finset.univ.filter fun i : Fin (3 * q) => ¬ m i = w).card = (3 * q - 1) := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (3 * q))))
        (p := fun i => m i = w)
      rw [h1, Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at this
      omega
    simp only [bnd, mul_ite]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_singleton]
    push_cast
    ring
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin (3 * q))) ×ˢ 𝒯, bnd x.1 (3 * x.2.card) * wtc_wt (q := q) (3 * x.2.card) =
      ∑ T ∈ 𝒯, (((3 * T.card).factorial * X (3 * T.card) + (3 * q - 1) * ((3 * T.card).factorial * Y (3 * T.card)) : ℕ) : ℝ)
        * wtc_wt (q := q) (3 * T.card) := by
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    dsimp only
    rw [← Finset.sum_mul, hsumcol]
  have step3 : ∑ T ∈ 𝒯, (((3 * T.card).factorial * X (3 * T.card) + (3 * q - 1) * ((3 * T.card).factorial * Y (3 * T.card)) : ℕ) : ℝ)
        * wtc_wt (q := q) (3 * T.card) = ∑ m ∈ Finset.range (q + 1), ((Nat.choose q m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ (q / 2) then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) := by
    rw [Finset.sum_filter, ← Finset.powerset_univ]
    have := Finset.sum_powerset_apply_card (fun m => if 1 ≤ m ∧ m ≤ (q / 2) then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) (x := (Finset.univ : Finset (Fin q)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := by rw [step2, step3]
    _ ≤ 1 / 50 := hvert

end

set_option maxRecDepth 100000 in
theorem wtc_avoid (hq : 3 ≤ q) (hodd : q % 2 = 1) (hpos : (∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ q / 2 then (3 * q : ℝ) * (((3 * (m + 1)).factorial * Nat.choose (3 * q / 2) (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0) ≤ 1 / 50)) (hvert : (∑ m ∈ Finset.range (q + 1), ((Nat.choose q m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ q / 2 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) ≤ 1 / 50)) (c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin (3 * q))) (m : Fin (3 * q) ≃ Fin (3 * q))
    (hm : ∀ (i : Fin (3 * q)) (v : Fin (3 * q)), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    ∃ σ : Equiv.Perm (Fin (3 * q)), ∀ t ∈ wtc_E c, ∃ v ∈ wtc_pos  t.2.1, σ v ≠ t.2.2 v := by
  classical
  have hmemE : ∀ t ∈ wtc_E c, 1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧ (∀ v ∉ wtc_pos  t.2.1, t.2.2 v = v) ∧
      Set.InjOn t.2.2 ↑(wtc_pos  t.2.1) ∧ w279_closed c t.1 ((wtc_pos  t.2.1).image t.2.2) := by
    intro t ht; exact wtc_mem_E.1 ht
  let D : ↥(wtc_E c) → Finset (Fin (3 * q)) := fun j => wtc_pos  j.1.2.1
  let f : ↥(wtc_E c) → Fin (3 * q) → Fin (3 * q) := fun j => j.1.2.2
  let x : ↥(wtc_E c) → ℝ := fun j => wtc_wt (q := q) (D j).card
  have hDcard : ∀ j : ↥(wtc_E c), 3 ≤ (D j).card ∧ (D j).card ≤ (3 * (q / 2)) := by
    intro j; have := hmemE j.1 j.2; simp only [D, wtc_card_pos ]; omega
  have hsumI : ∀ (P : (Fin (3 * q) × Finset (Fin q) × (Fin (3 * q) → Fin (3 * q))) → Prop) [DecidablePred P],
      ∑ j ∈ (Finset.univ : Finset ↥(wtc_E c)).filter (fun j => P j.1), x j =
        ∑ t ∈ (wtc_E c).filter P, wtc_wt (q := q) (wtc_pos  t.2.1).card := by
    intro P _
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_coe_sort (wtc_E c) (fun t => if P t then wtc_wt (q := q) (wtc_pos  t.2.1).card else 0)
  have hx0 : ∀ j, 0 ≤ x j := fun j => wtc_wt_nonneg  _
  have hx1 : ∀ j, x j < 1 := fun j => wtc_wt_lt_one hq _ (by have := hDcard j; omega) (hDcard j).2
  have hprob : ∀ i, (1 : ℝ) / (((3 * q) : ℕ).descFactorial (D i).card : ℝ) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
        ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))), (1 - x j) := by
    intro i
    set d := (D i).card with hd
    set N := Finset.univ.filter (fun j => j ≠ i ∧ (¬ Disjoint (D i) (D j) ∨
      ¬ Disjoint ((D i).image (f i)) ((D j).image (f j)))) with hN
    let Fsel : ↥(wtc_E c) → Fin (3 * q) ⊕ Fin (3 * q) := fun j =>
      if h : (D i ∩ D j).Nonempty then Sum.inl (Classical.choose h)
      else if h' : ((D i).image (f i) ∩ (D j).image (f j)).Nonempty then Sum.inr (Classical.choose h')
      else Sum.inl ⟨0, by omega⟩
    let S : Finset (Fin (3 * q) ⊕ Fin (3 * q)) :=
      (D i).map Function.Embedding.inl ∪ ((D i).image (f i)).map Function.Embedding.inr
    have hNmem : ∀ j ∈ N, (D i ∩ D j).Nonempty ∨ ((D i).image (f i) ∩ (D j).image (f j)).Nonempty := by
      intro j hj
      rw [hN, Finset.mem_filter] at hj
      rw [← Finset.not_disjoint_iff_nonempty_inter, ← Finset.not_disjoint_iff_nonempty_inter]
      exact hj.2.2
    have hfS : ∀ j ∈ N, Fsel j ∈ S := by
      intro j hj
      have h0 := hNmem j hj
      simp only [Fsel]
      split_ifs with h h'
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h)).1, rfl⟩))
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_map.2
          ⟨_, (Finset.mem_inter.1 (Classical.choose_spec h')).1, rfl⟩))
      · exact absurd h0 (by tauto)
    have hmass : ∀ r ∈ S, ∑ j ∈ N.filter (fun j => Fsel j = r), x j ≤ 1 / 50 := by
      intro r _
      rcases r with p | w
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(wtc_E c)).filter (fun j => p ∈ wtc_pos  j.1.2.1), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              · have := (Finset.mem_inter.1 (Classical.choose_spec h)).2
                rw [Sum.inl.injEq] at hF
                rw [← hF]; exact this
              · exact absurd h0 (by tauto)
          _ = _ := hsumI (fun t => p ∈ wtc_pos  t.2.1)
          _ ≤ _ := wtc_pos_mass hodd c m hm hpos p
      · calc _ ≤ ∑ j ∈ (Finset.univ : Finset ↥(wtc_E c)).filter
                (fun j => w ∈ (wtc_pos  j.1.2.1).image j.1.2.2), x j := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hx0 j)
              intro j hj
              rw [Finset.mem_filter] at hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              have h0 := hNmem j hj.1
              have hF := hj.2
              simp only [Fsel] at hF
              split_ifs at hF with h h'
              have := (Finset.mem_inter.1 (Classical.choose_spec h')).2
              rw [Sum.inr.injEq] at hF
              rw [← hF]; exact this
          _ = _ := hsumI (fun t => w ∈ (wtc_pos  t.2.1).image t.2.2)
          _ ≤ _ := wtc_vert_mass hodd c m hm hvert w
    have hfib := finite_product_one_sub_lower_bound_by_fibres N S Fsel x (1 / 50) (by norm_num) (by norm_num)
      (fun j _ => ⟨hx0 j, (hx1 j).le⟩) hfS hmass
    have hcardS : S.card ≤ 2 * d := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_map, Finset.card_map]
      have := Finset.card_image_le (s := D i) (f := f i)
      omega
    have hM : (1 - 1 / 50 : ℝ) ^ (2 * d) ≤ (1 - 1 / 50) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcardS
    have hpos : (0 : ℝ) < ((Nat.descFactorial (3 * q) d : ℕ) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.2 (by have := hDcard i; omega)
    change (1 : ℝ) / _ ≤ wtc_wt (q := q)  d * ∏ j ∈ N, (1 - x j)
    unfold wtc_wt 
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    calc (1 : ℝ) ≤ ((21 / 20 : ℝ) * (1 - 1 / 50) ^ 2) ^ d := one_le_pow₀ (by norm_num)
      _ = (21 / 20 : ℝ) ^ d * (1 - 1 / 50) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
      _ ≤ (21 / 20 : ℝ) ^ d * ∏ j ∈ N, (1 - x j) :=
        mul_le_mul_of_nonneg_left (hM.trans hfib) (by positivity)
  obtain ⟨σ, hσ⟩ := canonical_permutation_avoidance_of_local_lemma (3 * q) (by omega) D f
    (fun j => Finset.card_pos.1 (by have := hDcard j; omega)) (fun j => (hmemE j.1 j.2).2.2.2.1) x hx0 hx1 hprob
  exact ⟨σ, fun t ht => hσ ⟨t, ht⟩⟩

set_option maxRecDepth 100000 in

theorem wild_triple_partition_mass_criterion {q : ℕ} (hq : 3 ≤ q) (hodd : q % 2 = 1) (hpos : (∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ q / 2 then (3 * q : ℝ) * (((3 * (m + 1)).factorial * Nat.choose (3 * q / 2) (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0) ≤ 1 / 50)) (hvert : (∑ m ∈ Finset.range (q + 1), ((Nat.choose q m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ q / 2 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) ≤ 1 / 50)) (c : (⊤ : SimpleGraph (Fin (3 * q))).lineGraph.Coloring (Fin (3 * q))) (m : Fin (3 * q) ≃ Fin (3 * q))
    (hm : ∀ (i : Fin (3 * q)) (v : Fin (3 * q)), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin (3 * q))) c ≤ 2 * q := by
  classical
  obtain ⟨σ, hσ⟩ := wtc_avoid hq hodd hpos hvert c m hm
  have hup := simple_graph_wild_number_le_of_block_cut_condition (n := (3 * q)) (q := q) (by omega) c
    (fun v => wtc_blk (σ.symm v)) (fun b => σ ⟨3 * b.val, by omega⟩) ?_ ?_
  · have he : 3 * q - q = 2 * q := by omega
    simpa only [he] using hup
  · intro b
    show wtc_blk (σ.symm (σ _)) = b
    apply Fin.ext
    simp only [Equiv.symm_apply_apply, wtc_blk ]
    omega
  · intro e S hS hSu
    by_contra hcon
    have hno : ∀ u v (huv : u ≠ v), wtc_blk (σ.symm u) ∈ S → wtc_blk (σ.symm v) ∉ S →
        c ⟨s(u, v), wild_kn_mem huv⟩ ≠ c e := by
      intro u v huv hu hv hc; exact hcon ⟨u, v, huv, hu, hv, hc⟩
    have hScard : 1 ≤ S.card ∧ S.card ≤ (q - 1) := by
      refine ⟨Finset.card_pos.2 hS, ?_⟩
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ S, hSu⟩)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    set T := if S.card ≤ (q / 2) then S else Finset.univ \ S with hTdef
    have hT : 1 ≤ T.card ∧ T.card ≤ (q / 2) := by
      rw [hTdef]; split_ifs with h
      · omega
      · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]; omega
    have hTclosed : ∀ u w (huw : u ≠ w), wtc_blk (σ.symm u) ∈ T →
        c ⟨s(u, w), wild_kn_mem huw⟩ = c e → wtc_blk (σ.symm w) ∈ T := by
      intro u w huw hu hc
      rw [hTdef] at hu ⊢
      split_ifs at hu ⊢ with h
      · by_contra hw; exact hno u w huw hu hw hc
      · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hu ⊢
        intro hw
        refine hno w u (Ne.symm huw) hw hu ?_
        exact (w279_c_swap c (Ne.symm huw)).trans hc
    let gext : Fin (3 * q) → Fin (3 * q) := fun v => if v ∈ wtc_pos  T then σ v else v
    have himg : ∀ u, u ∈ (wtc_pos  T).image gext ↔ wtc_blk (σ.symm u) ∈ T := by
      intro u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
        simp only [gext, if_pos hv, Equiv.symm_apply_apply]
        exact wtc_mem_pos.1 hv
      · intro hu
        have hu' : σ.symm u ∈ wtc_pos  T := wtc_mem_pos.2 hu
        exact Finset.mem_image.2 ⟨σ.symm u, hu', by simp only [gext, if_pos hu', Equiv.apply_symm_apply]⟩
    have hmem : (c e, T, gext) ∈ wtc_E c := by
      rw [wtc_mem_E ]
      refine ⟨hT.1, hT.2, ?_, ?_, ?_⟩
      · intro v hv; simp only [gext, if_neg hv]
      · intro a ha b hb hab
        simp only [gext, Finset.mem_coe] at ha hb hab
        rw [if_pos ha, if_pos hb] at hab
        exact σ.injective hab
      · intro u hu w huw hc
        rw [himg] at hu ⊢
        exact hTclosed u w huw hu hc
    obtain ⟨v, hv, hne⟩ := hσ _ hmem
    simp only [gext] at hne
    exact hne (by rw [if_pos hv])
