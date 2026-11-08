import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.GStableKneserAdj
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_193_hom_cycle_step

Topic: graphs   Node: 3bb7098c84fc

Provenance: formalization of a published result. Source: arXiv:2610.17884 Lemma 2.12 -- The chromatic number of G-stable Kneser graphs

For all integers k ≥ 2 and r ≥ 2 * k - 2, there exists a graph homomorphism from the G-stable Kneser graph KG(C_{r+2} ⊔ K_1, k) to the G-stable Kneser graph KG(C_r ⊔ K_1, k-1).
-/

open Finset

def op_193_embed (r : ℕ) (hr : 0 < r) (x : Fin (r + 2) ⊕ Unit) : Fin r ⊕ Unit :=
  match x with
  | Sum.inr () => Sum.inr ()
  | Sum.inl u =>
    if h : u.val < r then Sum.inl ⟨u.val, h⟩
    else Sum.inl ⟨0, hr⟩

lemma op_193_inlPart_nonempty {r k : ℕ} (hk : 2 ≤ k) (s : Finset (Fin (r + 2) ⊕ Unit))
    (hs : s.card = k) :
    (s.preimage Sum.inl Sum.inl_injective.injOn).Nonempty := by
  by_contra h
  rw [Finset.nonempty_iff_ne_empty, not_not] at h
  have : s ⊆ {Sum.inr ()} := by
    intro x hx
    cases x with
    | inl u =>
      have hu : u ∈ s.preimage Sum.inl Sum.inl_injective.injOn := by simp [hx]
      rw [h] at hu; simp at hu
    | inr u => cases u; simp
  have hcard := Finset.card_le_card this
  simp only [Finset.card_singleton] at hcard
  omega

lemma op_193_cycle_indep_lt_r {r : ℕ} (hr : 2 ≤ r) (C : Finset (Fin (r + 2)))
    (hC_indep : (SimpleGraph.cycleGraph (r + 2)).IsIndepSet (C : Set (Fin (r + 2))))
    {m u : Fin (r + 2)} (hm : m ∈ C) (hu : u ∈ C) (hlt : u < m) :
    u.val < r := by
  by_contra hge
  have hu_lt := u.isLt
  have hm_lt := m.isLt
  have hu_val : u.val = r := by omega
  have hm_val : m.val = r + 1 := by omega
  have hadj : (SimpleGraph.cycleGraph (r + 2)).Adj u m := by
    rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
    have h1 : (r + 2 - u.val + m.val) % (r + 2) = 1 := by
      rw [hu_val, hm_val]
      have : r + 2 - r + (r + 1) = (r + 2) + 1 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    right; exact h1
  have hpair : ¬ (SimpleGraph.cycleGraph (r + 2)).Adj u m := by
    apply hC_indep hu hm
    intro h_eq
    rw [h_eq] at hlt
    exact lt_irrefl _ hlt
  exact hpair hadj

lemma op_193_embed_inj_on {r : ℕ} (hr : 0 < r)
    (s : Set (Fin (r + 2) ⊕ Unit))
    (hs : ∀ x ∈ s, ∀ u : Fin (r + 2), x = Sum.inl u → u.val < r) :
    s.InjOn (op_193_embed r hr) := by
  intro x hx y hy hxy
  cases x with
  | inr u =>
    cases u
    cases y with
    | inr v => cases v; rfl
    | inl v =>
      dsimp [op_193_embed] at hxy
      split_ifs at hxy
  | inl u =>
    cases y with
    | inr v =>
      cases v
      dsimp [op_193_embed] at hxy
      split_ifs at hxy
    | inl v =>
      have hu := hs (Sum.inl u) hx u rfl
      have hv := hs (Sum.inl v) hy v rfl
      dsimp [op_193_embed] at hxy
      rw [dif_pos hu, dif_pos hv] at hxy
      injection hxy with h1
      have hval : u.val = v.val := Fin.mk.inj h1
      exact congrArg Sum.inl (Fin.ext hval)

lemma op_193_sum_unit_not_adj_inr {V : Type*} (G : SimpleGraph V) (x : V ⊕ Unit) :
    ¬ (G.sum (⊥ : SimpleGraph Unit)).Adj (Sum.inr ()) x := by
  cases x <;> simp [SimpleGraph.sum]

lemma op_193_sum_unit_not_adj_inr' {V : Type*} (G : SimpleGraph V) (x : V ⊕ Unit) :
    ¬ (G.sum (⊥ : SimpleGraph Unit)).Adj x (Sum.inr ()) := by
  cases x <;> simp [SimpleGraph.sum]

lemma op_193_cycle_indep_step {r : ℕ} (hr : 2 ≤ r)
    (C : Finset (Fin (r + 2)))
    (hC_indep : (SimpleGraph.cycleGraph (r + 2)).IsIndepSet (C : Set (Fin (r + 2))))
    {m : Fin (r + 2)} (hm : m ∈ C) (hmax : ∀ x ∈ C, x ≤ m)
    {u v : Fin (r + 2)} (hu : u ∈ C) (hv : v ∈ C) (hum : u ≠ m) (hvm : v ≠ m)
    (huv : u < v) (hu_lt : u.val < r) (hv_lt : v.val < r) :
    ¬ (SimpleGraph.cycleGraph r).Adj ⟨u.val, hu_lt⟩ ⟨v.val, hv_lt⟩ := by
  have hadj_iff : (SimpleGraph.cycleGraph r).Adj ⟨u.val, hu_lt⟩ ⟨v.val, hv_lt⟩ ↔
      v.val - u.val = 1 ∨ (u.val = 0 ∧ v.val = r - 1) := by
    rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
    have h1 : (r - u.val + v.val) % r = v.val - u.val := by
      have : r - u.val + v.val = r + (v.val - u.val) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (r - v.val + u.val) % r = r - (v.val - u.val) := by
      have : r - v.val + u.val = r - (v.val - u.val) := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h2]
    constructor
    · rintro (h | h)
      · right; omega
      · left; exact h
    · rintro (h | ⟨h0, hr1⟩)
      · right; exact h
      · left; omega
  rw [hadj_iff]
  rintro (h1 | ⟨h0, hr1⟩)
  · have hadj_C : (SimpleGraph.cycleGraph (r + 2)).Adj u v := by
      rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
      have : (r + 2 - u.val + v.val) % (r + 2) = 1 := by
        have : r + 2 - u.val + v.val = (r + 2) + (v.val - u.val) := by omega
        rw [this, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      right; exact this
    have hnot : ¬ (SimpleGraph.cycleGraph (r + 2)).Adj u v := by
      apply hC_indep hu hv
      intro heq
      rw [heq] at huv
      exact lt_irrefl _ huv
    exact hnot hadj_C
  · have hvm_lt : v < m := lt_of_le_of_ne (hmax v hv) hvm
    have hm_val : m.val = r ∨ m.val = r + 1 := by
      have := m.isLt
      omega
    rcases hm_val with hm_r | hm_r1
    · have hadj_vm : (SimpleGraph.cycleGraph (r + 2)).Adj v m := by
        rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
        have : (r + 2 - v.val + m.val) % (r + 2) = 1 := by
          have : r + 2 - v.val + m.val = (r + 2) + 1 := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        right; exact this
      have hnot : ¬ (SimpleGraph.cycleGraph (r + 2)).Adj v m := by
        apply hC_indep hv hm
        intro heq
        exact hvm heq
      exact hnot hadj_vm
    · have hadj_um : (SimpleGraph.cycleGraph (r + 2)).Adj u m := by
        rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub]
        have : (r + 2 - m.val + u.val) % (r + 2) = 1 := by
          have : r + 2 - m.val + u.val = 1 := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
        left; exact this
      have hnot : ¬ (SimpleGraph.cycleGraph (r + 2)).Adj u m := by
        apply hC_indep hu hm
        intro heq
        exact hum heq
      exact hnot hadj_um

lemma op_193_embed_eq_iff {r : ℕ} (hr : 0 < r) (a b : Fin (r + 2) ⊕ Unit)
    (ha : ∀ u : Fin (r + 2), a = Sum.inl u → u.val < r)
    (hb : ∀ u : Fin (r + 2), b = Sum.inl u → u.val < r) :
    op_193_embed r hr a = op_193_embed r hr b ↔ a = b := by
  constructor
  · intro h
    cases a with
    | inr u =>
      cases u
      cases b with
      | inr v => cases v; rfl
      | inl v =>
        dsimp [op_193_embed] at h
        split_ifs at h
    | inl u =>
      cases b with
      | inr v =>
        cases v
        dsimp [op_193_embed] at h
        split_ifs at h
      | inl v =>
        have hua := ha u rfl
        have hub := hb v rfl
        dsimp [op_193_embed] at h
        rw [dif_pos hua, dif_pos hub] at h
        injection h with h1
        have hval : u.val = v.val := Fin.mk.inj h1
        exact congrArg Sum.inl (Fin.ext hval)
  · rintro rfl; rfl

noncomputable def op_193_fn (k r : ℕ) (hk : 2 ≤ k) (hr : 2 * k - 2 ≤ r)
    (s : { s : Finset (Fin (r + 2) ⊕ Unit) //
      ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s }) :
    Finset (Fin r ⊕ Unit) :=
  have hr_pos : 0 < r := by omega
  let C := s.1.preimage Sum.inl Sum.inl_injective.injOn
  have hC_ne : C.Nonempty := op_193_inlPart_nonempty hk s.1 s.2.card_eq
  let m := C.max' hC_ne
  (s.1.erase (Sum.inl m)).image (op_193_embed r hr_pos)

lemma op_193_fn_isNIndepSet (k r : ℕ) (hk : 2 ≤ k) (hr : 2 * k - 2 ≤ r)
    (s : { s : Finset (Fin (r + 2) ⊕ Unit) //
      ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s }) :
    ((SimpleGraph.cycleGraph r).sum (⊥ : SimpleGraph Unit)).IsNIndepSet (k - 1)
      (op_193_fn k r hk hr s) := by
  have hr_pos : 0 < r := by omega
  have hr2 : 2 ≤ r := by omega
  let C := s.1.preimage Sum.inl Sum.inl_injective.injOn
  have hC_ne : C.Nonempty := op_193_inlPart_nonempty hk s.1 s.2.card_eq
  let m := C.max' hC_ne
  have hm_in : Sum.inl m ∈ s.1 := Finset.mem_preimage.mp (Finset.max'_mem C hC_ne)
  let s' := s.1.erase (Sum.inl m)
  have hs'_card : s'.card = k - 1 := by
    rw [Finset.card_erase_of_mem hm_in, s.2.card_eq]
  have hs_cycle_indep : (SimpleGraph.cycleGraph (r + 2)).IsIndepSet (C : Set (Fin (r + 2))) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_preimage] at hu hv
    have : ¬ ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).Adj (Sum.inl u) (Sum.inl v) :=
      s.2.isIndepSet hu hv (by rintro ⟨⟩; exact huv rfl)
    exact this
  have hs'_lt : ∀ x ∈ s', ∀ u : Fin (r + 2), x = Sum.inl u → u.val < r := by
    intro x hx u hxu
    rw [Finset.mem_erase] at hx
    have hu_in : u ∈ C := by
      rw [Finset.mem_preimage, ← hxu]
      exact hx.2
    have hu_ne : u ≠ m := by
      rintro rfl
      exact hx.1 (by rw [hxu])
    have hu_le := Finset.le_max' C u hu_in
    have hu_lt : u < m := lt_of_le_of_ne hu_le hu_ne
    exact op_193_cycle_indep_lt_r hr2 C hs_cycle_indep (Finset.max'_mem C hC_ne) hu_in hu_lt
  have ht_card : (op_193_fn k r hk hr s).card = k - 1 := by
    dsimp [op_193_fn]
    have hinj : Set.InjOn (op_193_embed r hr_pos) ↑s' :=
      op_193_embed_inj_on hr_pos (↑s') (fun x hx u hxu => hs'_lt x (Finset.mem_coe.mp hx) u hxu)
    rw [Finset.card_image_of_injOn hinj, hs'_card]
  refine ⟨?_, ht_card⟩
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  change x ∈ op_193_fn k r hk hr s at hx
  change y ∈ op_193_fn k r hk hr s at hy
  dsimp [op_193_fn] at hx hy
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  have hab : a ≠ b := by
    rintro rfl
    exact hxy rfl
  cases a with
  | inr ua =>
    cases ua
    dsimp [op_193_embed]
    exact op_193_sum_unit_not_adj_inr _ _
  | inl ua =>
    cases b with
    | inr ub =>
      cases ub
      dsimp [op_193_embed]
      exact op_193_sum_unit_not_adj_inr' _ _
    | inl ub =>
      have hua_lt := hs'_lt (Sum.inl ua) ha ua rfl
      have hub_lt := hs'_lt (Sum.inl ub) hb ub rfl
      dsimp [op_193_embed]
      rw [dif_pos hua_lt, dif_pos hub_lt]
      rw [SimpleGraph.sum]
      dsimp
      have hua_in : ua ∈ C := by
        rw [Finset.mem_preimage]
        exact (Finset.mem_erase.mp ha).2
      have hub_in : ub ∈ C := by
        rw [Finset.mem_preimage]
        exact (Finset.mem_erase.mp hb).2
      have hua_ne : ua ≠ m := by
        intro heq
        have := (Finset.mem_erase.mp ha).1
        exact this (congrArg Sum.inl heq)
      have hub_ne : ub ≠ m := by
        intro heq
        have := (Finset.mem_erase.mp hb).1
        exact this (congrArg Sum.inl heq)
      have huab : ua ≠ ub := by
        intro heq
        exact hab (congrArg Sum.inl heq)
      rcases lt_or_gt_of_ne huab with hlt | hgt
      · exact op_193_cycle_indep_step hr2 C hs_cycle_indep (Finset.max'_mem C hC_ne)
          (Finset.le_max' C) hua_in hub_in hua_ne hub_ne hlt hua_lt hub_lt
      · intro hadj
        have hadj_symm := hadj.symm
        exact op_193_cycle_indep_step hr2 C hs_cycle_indep (Finset.max'_mem C hC_ne)
          (Finset.le_max' C) hub_in hua_in hub_ne hua_ne hgt hub_lt hua_lt hadj_symm

/-- Homomorphism from KG(C_{r+2} ⊔ K_1, k) to KG(C_r ⊔ K_1, k-1). -/
theorem op_193_hom_cycle_step (k r : ℕ) (hk : 2 ≤ k) (hr : 2 * k - 2 ≤ r) :
    Nonempty (GStableKneser ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)) k →g
              GStableKneser ((SimpleGraph.cycleGraph r).sum (⊥ : SimpleGraph Unit)) (k - 1)) := by
  have hr_pos : 0 < r := by omega
  have hr2 : 2 ≤ r := by omega
  let F : { s : Finset (Fin (r + 2) ⊕ Unit) //
            ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s } →
          { t : Finset (Fin r ⊕ Unit) //
            ((SimpleGraph.cycleGraph r).sum (⊥ : SimpleGraph Unit)).IsNIndepSet (k - 1) t } :=
    fun s => ⟨op_193_fn k r hk hr s, op_193_fn_isNIndepSet k r hk hr s⟩
  refine ⟨⟨F, ?_⟩⟩
  intro s t hadj
  rw [g_stable_kneser_adj] at hadj ⊢
  have hdisj : Disjoint s.1 t.1 := hadj.1
  have hdisj' : Disjoint (op_193_fn k r hk hr s) (op_193_fn k r hk hr t) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    dsimp [op_193_fn] at hz1 hz2
    rw [Finset.mem_image] at hz1 hz2
    rcases hz1 with ⟨a, ha, rfl⟩
    rcases hz2 with ⟨b, hb, hzb⟩
    have ha_in : a ∈ s.1 := (Finset.mem_erase.mp ha).2
    have hb_in : b ∈ t.1 := (Finset.mem_erase.mp hb).2
    have ha_lt : ∀ u : Fin (r + 2), a = Sum.inl u → u.val < r := by
      intro u hu
      have hu_in : u ∈ s.1.preimage Sum.inl Sum.inl_injective.injOn := by
        rw [Finset.mem_preimage, ← hu]; exact ha_in
      have hu_ne : u ≠ (s.1.preimage Sum.inl Sum.inl_injective.injOn).max' (op_193_inlPart_nonempty hk s.1 s.2.card_eq) := by
        rintro rfl
        exact (Finset.mem_erase.mp ha).1 (by rw [hu])
      have hu_le := Finset.le_max' _ u hu_in
      have hu_lt' : u < _ := lt_of_le_of_ne hu_le hu_ne
      have hs_indep : (SimpleGraph.cycleGraph (r + 2)).IsIndepSet
          ((s.1.preimage Sum.inl Sum.inl_injective.injOn : Finset (Fin (r + 2))) : Set (Fin (r + 2))) := by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_preimage] at hx hy
        have : ¬ ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).Adj (Sum.inl x) (Sum.inl y) :=
          s.2.isIndepSet hx hy (by rintro ⟨⟩; exact hxy rfl)
        exact this
      exact op_193_cycle_indep_lt_r hr2 _ hs_indep (Finset.max'_mem _ _) hu_in hu_lt'
    have hb_lt : ∀ u : Fin (r + 2), b = Sum.inl u → u.val < r := by
      intro u hu
      have hu_in : u ∈ t.1.preimage Sum.inl Sum.inl_injective.injOn := by
        rw [Finset.mem_preimage, ← hu]; exact hb_in
      have hu_ne : u ≠ (t.1.preimage Sum.inl Sum.inl_injective.injOn).max' (op_193_inlPart_nonempty hk t.1 t.2.card_eq) := by
        rintro rfl
        exact (Finset.mem_erase.mp hb).1 (by rw [hu])
      have hu_le := Finset.le_max' _ u hu_in
      have hu_lt' : u < _ := lt_of_le_of_ne hu_le hu_ne
      have ht_indep : (SimpleGraph.cycleGraph (r + 2)).IsIndepSet
          ((t.1.preimage Sum.inl Sum.inl_injective.injOn : Finset (Fin (r + 2))) : Set (Fin (r + 2))) := by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_preimage] at hx hy
        have : ¬ ((SimpleGraph.cycleGraph (r + 2)).sum (⊥ : SimpleGraph Unit)).Adj (Sum.inl x) (Sum.inl y) :=
          t.2.isIndepSet hx hy (by rintro ⟨⟩; exact hxy rfl)
        exact this
      exact op_193_cycle_indep_lt_r hr2 _ ht_indep (Finset.max'_mem _ _) hu_in hu_lt'
    have heq : a = b := (op_193_embed_eq_iff hr_pos a b ha_lt hb_lt).mp hzb.symm
    rw [heq] at ha_in
    exact (Finset.disjoint_left.mp hdisj ha_in) hb_in
  refine ⟨hdisj', ?_⟩
  rintro heq
  have hcard : (op_193_fn k r hk hr s).card = k - 1 := (op_193_fn_isNIndepSet k r hk hr s).card_eq
  have hne : (op_193_fn k r hk hr s).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at hcard
    omega
  rcases hne with ⟨x, hx_s⟩
  have heq1 : (F s).1 = (F t).1 := congrArg Subtype.val heq
  change op_193_fn k r hk hr s = op_193_fn k r hk hr t at heq1
  have hx_t : x ∈ op_193_fn k r hk hr t := by rw [← heq1]; exact hx_s
  exact (Finset.disjoint_left.mp hdisj' hx_s) hx_t
