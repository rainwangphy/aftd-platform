import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_193_cycle_isolated_vertex_chromatic_le

Topic: graphs   Node: c66f8486030a

Provenance: formalization of a published result. Source: scout/2610-17884-the-chromatic-number-of-g-stable-kneser-graphs.md:112

For any natural numbers k ≥ 3 and m ≥ 4 * k - 3, the chromatic number of the G-stable Kneser graph of the disjoint sum of the m-cycle and an isolated vertex is at most m - 2 * k + 3.
-/

open Finset

noncomputable def op_193_cycle_isolated_vertex_chromatic_le_inlPart {m : ℕ}
    (S : Finset (Fin m ⊕ Unit)) : Finset (Fin m) :=
  S.preimage Sum.inl (by
    intro a ha b hb hab
    exact Sum.inl_injective hab)

lemma op_193_cycle_isolated_vertex_chromatic_le_mem_inlPart {m : ℕ}
    (S : Finset (Fin m ⊕ Unit)) (a : Fin m) :
    a ∈ op_193_cycle_isolated_vertex_chromatic_le_inlPart S ↔ Sum.inl a ∈ S := by
  unfold op_193_cycle_isolated_vertex_chromatic_le_inlPart
  exact Finset.mem_preimage

lemma op_193_cycle_isolated_vertex_chromatic_le_card_inlPart {m : ℕ}
    (S : Finset (Fin m ⊕ Unit)) (h : (Sum.inr () : Fin m ⊕ Unit) ∉ S) :
    (op_193_cycle_isolated_vertex_chromatic_le_inlPart S).card = S.card := by
  have hmap :
      (op_193_cycle_isolated_vertex_chromatic_le_inlPart S).map
        ⟨Sum.inl, Sum.inl_injective⟩ = S := by
    ext x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (op_193_cycle_isolated_vertex_chromatic_le_mem_inlPart S a).mp ha
    · intro hx
      rcases x with a | u
      · exact ⟨a, (op_193_cycle_isolated_vertex_chromatic_le_mem_inlPart S a).mpr hx, rfl⟩
      · exact absurd hx (by simpa using h)
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map] at hc
  exact hc

noncomputable def op_193_cycle_isolated_vertex_chromatic_le_mmin {m : ℕ}
    (A : Finset (Fin m)) (fb : Fin m) : Fin m :=
  (A ∪ {fb}).min' ⟨fb, Finset.mem_union_right _ (Finset.mem_singleton_self fb)⟩

lemma op_193_cycle_isolated_vertex_chromatic_le_mmin_mem {m : ℕ}
    (A : Finset (Fin m)) (fb : Fin m) :
    op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ∈ A ∪ {fb} :=
  Finset.min'_mem _ _

lemma op_193_cycle_isolated_vertex_chromatic_le_mmin_le {m : ℕ}
    (A : Finset (Fin m)) (fb : Fin m) :
    op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ≤ fb :=
  Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self fb))

lemma op_193_cycle_isolated_vertex_chromatic_le_mmin_le_of_mem {m : ℕ}
    {A : Finset (Fin m)} {fb : Fin m} {a : Fin m} (ha : a ∈ A) :
    op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ≤ a :=
  Finset.min'_le _ _ (Finset.mem_union_left _ ha)

lemma op_193_cycle_isolated_vertex_chromatic_le_mmin_val_le {m : ℕ}
    (A : Finset (Fin m)) (fb : Fin m) :
    (op_193_cycle_isolated_vertex_chromatic_le_mmin A fb).val ≤ fb.val :=
  op_193_cycle_isolated_vertex_chromatic_le_mmin_le A fb

lemma op_193_cycle_isolated_vertex_chromatic_le_core_min_ne {m k : ℕ}
    (A B : Finset (Fin m)) (hdisj : Disjoint A B) (hA : A.card = k) (hB : B.card = k)
    (fb : Fin m) (hfbval : fb.val = m - 2*k + 1) :
    op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ≠
      op_193_cycle_isolated_vertex_chromatic_le_mmin B fb := by
  intro heq
  by_cases hAfb : op_193_cycle_isolated_vertex_chromatic_le_mmin A fb = fb
  · have hBfb : op_193_cycle_isolated_vertex_chromatic_le_mmin B fb = fb := by
      rw [← heq]; exact hAfb
    have hAsub : A ⊆ Finset.Ici fb := by
      intro a ha
      rw [Finset.mem_Ici]
      calc fb = op_193_cycle_isolated_vertex_chromatic_le_mmin A fb := hAfb.symm
        _ ≤ a := op_193_cycle_isolated_vertex_chromatic_le_mmin_le_of_mem ha
    have hBsub : B ⊆ Finset.Ici fb := by
      intro a ha
      rw [Finset.mem_Ici]
      calc fb = op_193_cycle_isolated_vertex_chromatic_le_mmin B fb := hBfb.symm
        _ ≤ a := op_193_cycle_isolated_vertex_chromatic_le_mmin_le_of_mem ha
    have hunion : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
    have hunionsub : A ∪ B ⊆ Finset.Ici fb := Finset.union_subset hAsub hBsub
    have hle : (A ∪ B).card ≤ (Finset.Ici fb).card := Finset.card_le_card hunionsub
    rw [hunion, hA, hB, Fin.card_Ici, hfbval] at hle
    omega
  · have hBfb : op_193_cycle_isolated_vertex_chromatic_le_mmin B fb ≠ fb := by
      rw [← heq]; exact hAfb
    have hA_mem : op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ∈ A := by
      have h := op_193_cycle_isolated_vertex_chromatic_le_mmin_mem A fb
      rcases Finset.mem_union.mp h with h | h
      · exact h
      · rw [Finset.mem_singleton] at h
        exact absurd h hAfb
    have hB_mem : op_193_cycle_isolated_vertex_chromatic_le_mmin B fb ∈ B := by
      have h := op_193_cycle_isolated_vertex_chromatic_le_mmin_mem B fb
      rcases Finset.mem_union.mp h with h | h
      · exact h
      · rw [Finset.mem_singleton] at h
        exact absurd h hBfb
    have hnot : op_193_cycle_isolated_vertex_chromatic_le_mmin A fb ∉ B :=
      Finset.disjoint_left.mp hdisj hA_mem
    exact hnot (heq ▸ hB_mem)

noncomputable def op_193_cycle_isolated_vertex_chromatic_le_colorFin (k m : ℕ)
    (hfb : m - 2*k + 1 < m)
    (v : { s : Finset (Fin m ⊕ Unit) //
      ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s }) :
    Fin (m - 2*k + 3) :=
  if hin : (Sum.inr () : Fin m ⊕ Unit) ∈ v.1 then
    ⟨m - 2*k + 2, by omega⟩
  else
    ⟨(op_193_cycle_isolated_vertex_chromatic_le_mmin
        (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1) ⟨m - 2*k + 1, hfb⟩).val, by
      have h1 : (op_193_cycle_isolated_vertex_chromatic_le_mmin
          (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1)
          ⟨m - 2*k + 1, hfb⟩).val ≤ m - 2*k + 1 :=
        op_193_cycle_isolated_vertex_chromatic_le_mmin_val_le
          (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1) ⟨m - 2*k + 1, hfb⟩
      omega⟩

lemma op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_mem (k m : ℕ)
    (hfb : m - 2*k + 1 < m)
    (v : { s : Finset (Fin m ⊕ Unit) //
      ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s })
    (h : (Sum.inr () : Fin m ⊕ Unit) ∈ v.1) :
    (op_193_cycle_isolated_vertex_chromatic_le_colorFin k m hfb v).val = m - 2*k + 2 := by
  unfold op_193_cycle_isolated_vertex_chromatic_le_colorFin
  rw [dif_pos h]

lemma op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_not_mem (k m : ℕ)
    (hfb : m - 2*k + 1 < m)
    (v : { s : Finset (Fin m ⊕ Unit) //
      ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)).IsNIndepSet k s })
    (h : (Sum.inr () : Fin m ⊕ Unit) ∉ v.1) :
    (op_193_cycle_isolated_vertex_chromatic_le_colorFin k m hfb v).val =
      (op_193_cycle_isolated_vertex_chromatic_le_mmin
        (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1) ⟨m - 2*k + 1, hfb⟩).val := by
  unfold op_193_cycle_isolated_vertex_chromatic_le_colorFin
  rw [dif_neg h]

/-- General upper bound for OP-193: the chromatic number of KG(C_m ⊔ K_1, k) is at most m - 2k + 3. -/
theorem op_193_cycle_isolated_vertex_chromatic_le
    (k m : ℕ) (hk : 3 ≤ k) (hm : 4 * k - 3 ≤ m) :
    (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber ≤
      m - 2 * k + 3 := by
  have hfb : m - 2*k + 1 < m := by omega
  apply SimpleGraph.Colorable.chromaticNumber_le
  refine ⟨SimpleGraph.Coloring.mk (op_193_cycle_isolated_vertex_chromatic_le_colorFin k m hfb) ?_⟩
  intro v w hadj
  have hdisj : Disjoint v.1 w.1 := hadj.1
  intro heq
  have hvaleq : (op_193_cycle_isolated_vertex_chromatic_le_colorFin k m hfb v).val =
      (op_193_cycle_isolated_vertex_chromatic_le_colorFin k m hfb w).val := by
    rw [heq]
  by_cases hv : (Sum.inr () : Fin m ⊕ Unit) ∈ v.1
  · by_cases hw : (Sum.inr () : Fin m ⊕ Unit) ∈ w.1
    · exact (Finset.disjoint_left.mp hdisj hv) hw
    · rw [op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_mem k m hfb v hv,
          op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_not_mem k m hfb w hw] at hvaleq
      have hwle : (op_193_cycle_isolated_vertex_chromatic_le_mmin
          (op_193_cycle_isolated_vertex_chromatic_le_inlPart w.1)
          ⟨m - 2*k + 1, hfb⟩).val ≤ m - 2*k + 1 :=
        op_193_cycle_isolated_vertex_chromatic_le_mmin_val_le _ _
      omega
  · by_cases hw : (Sum.inr () : Fin m ⊕ Unit) ∈ w.1
    · rw [op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_not_mem k m hfb v hv,
          op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_mem k m hfb w hw] at hvaleq
      have hvle : (op_193_cycle_isolated_vertex_chromatic_le_mmin
          (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1)
          ⟨m - 2*k + 1, hfb⟩).val ≤ m - 2*k + 1 :=
        op_193_cycle_isolated_vertex_chromatic_le_mmin_val_le _ _
      omega
    · rw [op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_not_mem k m hfb v hv,
          op_193_cycle_isolated_vertex_chromatic_le_colorFin_val_of_not_mem k m hfb w hw] at hvaleq
      have hAcard : (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1).card = k := by
        rw [op_193_cycle_isolated_vertex_chromatic_le_card_inlPart v.1 hv, v.2.card_eq]
      have hBcard : (op_193_cycle_isolated_vertex_chromatic_le_inlPart w.1).card = k := by
        rw [op_193_cycle_isolated_vertex_chromatic_le_card_inlPart w.1 hw, w.2.card_eq]
      have hAdisj : Disjoint (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1)
          (op_193_cycle_isolated_vertex_chromatic_le_inlPart w.1) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [op_193_cycle_isolated_vertex_chromatic_le_mem_inlPart] at ha hb
        exact (Finset.disjoint_left.mp hdisj ha) hb
      have hne := op_193_cycle_isolated_vertex_chromatic_le_core_min_ne
        (op_193_cycle_isolated_vertex_chromatic_le_inlPart v.1)
        (op_193_cycle_isolated_vertex_chromatic_le_inlPart w.1)
        hAdisj hAcard hBcard ⟨m - 2*k + 1, hfb⟩ rfl
      exact hne (Fin.ext hvaleq)
