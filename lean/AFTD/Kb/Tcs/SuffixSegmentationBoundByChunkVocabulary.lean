import AFTD.Prelude
import AFTD.Kb.Tcs.WordSubstrings
import AFTD.Kb.Tcs.WordSuffixes
import AFTD.Kb.Tcs.IsTokenSegmentation
import AFTD.Kb.Tcs.ChunkTokenBoundLe
import AFTD.Kb.Tcs.ChunkInnerTokenBoundLe

/-!
# suffix_segmentation_bound_by_chunk_vocabulary

Topic: approximation   Node: 544755092db8

Provenance: formalization of a published result. Source: arXiv:2611.15074 Lemma 3.8 -- Tokenization: Hardness and Bicriteria Approximation Algorithms

Fix q in {2, ..., M}. For every alphabet and every nonempty word w of length at most M, there exists a vocabulary V_w of substrings of w of length at least 2 with size at most q such that every nonempty suffix y of w can be segmented into at most q - 1 + ⌈M / q⌉ tokens from V_w and singletons.
-/

private def suffix_segmentation_bound_by_chunk_vocabulary_prop {α : Type*} (r q : ℕ)
    (V : Finset (List α)) (w : List α) : Prop :=
  ∀ (m : ℕ) (y : List α), w.drop m = y → y ≠ [] →
    ((m % r = 0 → ∃ tokens : List (List α),
        is_token_segmentation (↑V : Set (List α)) y tokens ∧ tokens.length ≤ q) ∧
     (m % r ≠ 0 → ∃ tokens : List (List α),
        is_token_segmentation (↑V : Set (List α)) y tokens ∧ tokens.length ≤ (r - 1) + (q - 1)))

private lemma suffix_segmentation_bound_by_chunk_vocabulary_singletons {α : Type*} (l : List α) :
    (l.map (fun a => [a])).flatten = l := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

private lemma suffix_segmentation_bound_by_chunk_vocabulary_seg_singletons {α : Type*}
    (V : Set (List α)) (y : List α) :
    is_token_segmentation V y (y.map (fun a => [a])) := by
  unfold is_token_segmentation
  constructor
  · rw [suffix_segmentation_bound_by_chunk_vocabulary_singletons]
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨a, _, rfl⟩ := ht
    exact Or.inr (by simp)

private lemma suffix_segmentation_bound_by_chunk_vocabulary_seg_append {α : Type*}
    (V : Set (List α)) (a b : List α) (ta tb : List (List α))
    (ha : is_token_segmentation V a ta) (hb : is_token_segmentation V b tb) :
    is_token_segmentation V (a ++ b) (ta ++ tb) := by
  unfold is_token_segmentation at *
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  constructor
  · rw [List.flatten_append, h1, h3]
  · intro t ht
    simp only [List.mem_append] at ht
    rcases ht with h | h
    · exact h2 t h
    · exact h4 t h

private lemma suffix_segmentation_bound_by_chunk_vocabulary_seg_mono {α : Type*}
    (V W : Set (List α)) (hVW : V ⊆ W) (y : List α) (t : List (List α))
    (h : is_token_segmentation V y t) : is_token_segmentation W y t := by
  unfold is_token_segmentation at *
  exact ⟨h.1, fun u hu => (h.2 u hu).imp (fun hv => hVW hv) id⟩

private theorem suffix_segmentation_bound_by_chunk_vocabulary_base {α : Type*} (r : ℕ) (w : List α)
    (hw : w.length ≤ 1 * r) :
    ∃ V : Finset (List α),
      (∀ u ∈ V, u <:+: w ∧ 2 ≤ u.length) ∧ V.card ≤ 1 ∧
        suffix_segmentation_bound_by_chunk_vocabulary_prop r 1 V w := by
  classical
  let V : Finset (List α) := if 2 ≤ w.length then {w} else ∅
  refine ⟨V, ?_, ?_, ?_⟩
  · intro u hu
    by_cases h2 : 2 ≤ w.length
    · simp only [V, h2, if_true, Finset.mem_singleton] at hu
      rw [hu]
      exact ⟨List.infix_refl w, h2⟩
    · simp [V, h2] at hu
  · simp only [V]
    by_cases h2 : 2 ≤ w.length <;> simp [h2]
  · rw [suffix_segmentation_bound_by_chunk_vocabulary_prop]
    intro m y hmy hyne
    have hmlt : m < w.length := by
      by_contra h
      push Not at h
      exact hyne (by rw [← hmy]; exact List.drop_eq_nil_of_le h)
    have hwr : w.length ≤ r := by simpa using hw
    have hmr : m < r := by omega
    have hleny : y.length = w.length - m := by rw [← hmy, List.length_drop]
    constructor
    · intro hm0
      have hm0' : m = 0 := by
        have := Nat.mod_eq_of_lt hmr
        omega
      have hyw : y = w := by rw [← hmy, hm0', List.drop_zero]
      refine ⟨[w], ?_, by simp⟩
      rw [hyw]
      unfold is_token_segmentation
      constructor
      · simp
      · intro t ht
        simp only [List.mem_singleton] at ht
        rw [ht]
        by_cases h2 : 2 ≤ w.length
        · left
          simp [V, h2]
        · right
          have h1 : w.length < 2 := by omega
          omega
    · intro hm0
      refine ⟨y.map (fun a => [a]), suffix_segmentation_bound_by_chunk_vocabulary_seg_singletons _ y, ?_⟩
      rw [List.length_map, hleny]
      have hmne : m ≠ 0 := by intro hc; exact hm0 (by rw [hc, Nat.zero_mod])
      have hm1 : 1 ≤ m := by omega
      have hle : w.length - m ≤ r - 1 :=
        (Nat.sub_le_sub_right hwr m).trans (Nat.sub_le_sub_left hm1 r)
      simpa using hle

private theorem suffix_segmentation_bound_by_chunk_vocabulary_step {α : Type*} (r q : ℕ)
    (hr : 1 ≤ r) (hq : 1 ≤ q) (w : List α) (hw : w.length ≤ (q + 1) * r)
    (ih : ∀ (w' : List α), w'.length ≤ q * r →
        ∃ V : Finset (List α),
          (∀ u ∈ V, u <:+: w' ∧ 2 ≤ u.length) ∧ V.card ≤ q ∧
            suffix_segmentation_bound_by_chunk_vocabulary_prop r q V w') :
    ∃ V : Finset (List α),
      (∀ u ∈ V, u <:+: w ∧ 2 ≤ u.length) ∧ V.card ≤ q + 1 ∧
        suffix_segmentation_bound_by_chunk_vocabulary_prop r (q + 1) V w := by
  classical
  let c : List α := w.take r
  let rest : List α := w.drop r
  have hwdecomp : w = c ++ rest := (List.take_append_drop r w).symm
  have hrest : rest.length ≤ q * r := by
    have hlen : rest.length = w.length - r := by
      show (w.drop r).length = _; rw [List.length_drop]
    rw [Nat.succ_mul] at hw
    rw [hlen]
    omega
  obtain ⟨Vr, hmemr, hcardr, hpropr⟩ := ih rest hrest
  let V : Finset (List α) := if 2 ≤ c.length then insert c Vr else Vr
  have hsub : (↑Vr : Set (List α)) ⊆ (↑V : Set (List α)) := by
    intro x hx
    rw [Finset.mem_coe] at hx ⊢
    by_cases h2 : 2 ≤ c.length
    · simp only [V, h2, if_true]; exact Finset.mem_insert_of_mem hx
    · simp only [V, h2, if_false]; exact hx
  have hcinfix : c <:+: w := ⟨[], rest, by rw [List.nil_append]; exact List.take_append_drop r w⟩
  have hrestsuffix : rest <:+ w := ⟨c, List.take_append_drop r w⟩
  refine ⟨V, ?_, ?_, ?_⟩
  · intro u hu
    by_cases h2 : 2 ≤ c.length
    · simp only [V, h2, if_true, Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact ⟨hcinfix, h2⟩
      · obtain ⟨hinf, hlen⟩ := hmemr u hu
        exact ⟨hinf.trans hrestsuffix.isInfix, hlen⟩
    · simp only [V, h2, if_false] at hu
      obtain ⟨hinf, hlen⟩ := hmemr u hu
      exact ⟨hinf.trans hrestsuffix.isInfix, hlen⟩
  · by_cases h2 : 2 ≤ c.length
    · simp only [V, h2, if_true]
      calc (insert c Vr).card ≤ Vr.card + 1 := Finset.card_insert_le _ _
        _ ≤ q + 1 := by omega
    · simp only [V, h2, if_false]; omega
  · rw [suffix_segmentation_bound_by_chunk_vocabulary_prop]
    intro m y hmy hyne
    have hmlt : m < w.length := by
      by_contra h
      push Not at h
      exact hyne (by rw [← hmy]; exact List.drop_eq_nil_of_le h)
    constructor
    · intro hmr0
      by_cases hmltr : m < r
      · have hm0 : m = 0 := by
          have hh : m % r = m := Nat.mod_eq_of_lt hmltr
          rw [hh] at hmr0
          exact hmr0
        have hyw : y = w := by rw [← hmy, hm0, List.drop_zero]
        have hwpos : 0 < w.length := Nat.lt_of_le_of_lt (Nat.zero_le m) hmlt
        have hclen : 0 < c.length := by
          rw [show c = w.take r from rfl, List.length_take]
          exact Nat.lt_min.mpr ⟨by omega, hwpos⟩
        have hsegc : is_token_segmentation (↑V : Set (List α)) c [c] := by
          unfold is_token_segmentation
          refine ⟨by simp, ?_⟩
          intro t ht
          simp only [List.mem_singleton] at ht
          rw [ht]
          by_cases h2 : 2 ≤ c.length
          · left
            rw [Finset.mem_coe]
            simp only [V, h2, if_true]
            exact Finset.mem_insert_self c Vr
          · right; omega
        by_cases hrestne : rest = []
        · have hyc : y = c := by rw [hyw, hwdecomp, hrestne, List.append_nil]
          refine ⟨[c], ?_, by simp⟩
          rw [hyc]; exact hsegc
        · obtain ⟨tr, hsegr, hlenr⟩ := (hpropr 0 rest List.drop_zero hrestne).1 (Nat.zero_mod r)
          refine ⟨[c] ++ tr, ?_, ?_⟩
          · rw [hyw, hwdecomp]
            exact suffix_segmentation_bound_by_chunk_vocabulary_seg_append _ _ _ _ _ hsegc
              (suffix_segmentation_bound_by_chunk_vocabulary_seg_mono _ _ hsub _ _ hsegr)
          · rw [List.length_append, List.length_singleton]; omega
      · have hmod : (m - r) % r = m % r := by
          conv_rhs => rw [show m = (m - r) + r by omega]
          rw [Nat.add_mod_right]
        have hdrop : rest.drop (m - r) = y := by
          rw [show rest = w.drop r from rfl, List.drop_drop,
            show r + (m - r) = m by omega, hmy]
        obtain ⟨tokens, hseg, hlen⟩ :=
          (hpropr (m - r) y hdrop hyne).1 (by rw [hmod]; exact hmr0)
        exact ⟨tokens, suffix_segmentation_bound_by_chunk_vocabulary_seg_mono _ _ hsub _ _ hseg,
          by omega⟩
    · intro hmr0
      by_cases hmltr : m < r
      · have hm1 : 1 ≤ m := by
          have hmne : m ≠ 0 := by intro hc; exact hmr0 (by rw [hc, Nat.zero_mod])
          omega
        have hcmlen : m < c.length := by
          rw [show c = w.take r from rfl, List.length_take]
          exact Nat.lt_min.mpr ⟨hmltr, hmlt⟩
        have hy : y = c.drop m ++ rest := by
          rw [← hmy, show w = c ++ rest from hwdecomp, List.drop_append]
          have hzero : m - c.length = 0 := by omega
          rw [hzero, List.drop_zero]
        have hlen1 : (c.drop m).length ≤ r - 1 := by
          rw [List.length_drop]
          have hc_le : c.length ≤ r := by
            rw [show c = w.take r from rfl, List.length_take]; exact min_le_left _ _
          exact (Nat.sub_le_sub_right hc_le m).trans (Nat.sub_le_sub_left hm1 r)
        by_cases hrestne : rest = []
        · have hy' : y = c.drop m := by rw [hy, hrestne, List.append_nil]
          refine ⟨(c.drop m).map (fun a => [a]), ?_, ?_⟩
          · rw [hy']; exact suffix_segmentation_bound_by_chunk_vocabulary_seg_singletons _ _
          · rw [List.length_map]; omega
        · obtain ⟨tr, hsegr, hlenr⟩ := (hpropr 0 rest List.drop_zero hrestne).1 (Nat.zero_mod r)
          refine ⟨(c.drop m).map (fun a => [a]) ++ tr, ?_, ?_⟩
          · rw [hy]
            exact suffix_segmentation_bound_by_chunk_vocabulary_seg_append _ _ _ _ _
              (suffix_segmentation_bound_by_chunk_vocabulary_seg_singletons _ _)
              (suffix_segmentation_bound_by_chunk_vocabulary_seg_mono _ _ hsub _ _ hsegr)
          · rw [List.length_append, List.length_map]; omega
      · have hmod : (m - r) % r = m % r := by
          conv_rhs => rw [show m = (m - r) + r by omega]
          rw [Nat.add_mod_right]
        have hdrop : rest.drop (m - r) = y := by
          rw [show rest = w.drop r from rfl, List.drop_drop,
            show r + (m - r) = m by omega, hmy]
        obtain ⟨tokens, hseg, hlen⟩ :=
          (hpropr (m - r) y hdrop hyne).2 (by rw [hmod]; exact hmr0)
        exact ⟨tokens, suffix_segmentation_bound_by_chunk_vocabulary_seg_mono _ _ hsub _ _ hseg,
          by omega⟩

private theorem suffix_segmentation_bound_by_chunk_vocabulary_aux {α : Type*} (r : ℕ) (hr : 1 ≤ r) :
    ∀ q : ℕ, 1 ≤ q → ∀ w : List α, w.length ≤ q * r →
      ∃ V : Finset (List α),
        (∀ u ∈ V, u <:+: w ∧ 2 ≤ u.length) ∧ V.card ≤ q ∧
          suffix_segmentation_bound_by_chunk_vocabulary_prop r q V w := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => intro w hw; exact suffix_segmentation_bound_by_chunk_vocabulary_base r w hw
  | succ q hq ih =>
      intro w hw
      exact suffix_segmentation_bound_by_chunk_vocabulary_step r q hr hq w hw ih

/-- arXiv:2611.15074 Lemma 3.8: Suffix segmentation bound by chunk vocabulary. -/
theorem suffix_segmentation_bound_by_chunk_vocabulary {α : Type*} (M q : ℕ)
    (hq : 2 ≤ q) (hqM : q ≤ M) (w : List α) (hw : w ≠ []) (hl : w.length ≤ M) :
    ∃ V_w : Finset (List α),
      (∀ u ∈ V_w, u ∈ word_substrings w) ∧
      V_w.card ≤ q ∧
      ∀ y ∈ word_suffixes w,
        ∃ tokens : List (List α),
          is_token_segmentation (↑V_w) y tokens ∧
          tokens.length ≤ q - 1 + M ⌈/⌉ q := by
  classical
  set r : ℕ := w.length ⌈/⌉ q with hrdef
  have hr : 1 ≤ r := by
    rw [hrdef, Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos
    · have : 0 < w.length := List.length_pos_iff.mpr hw
      omega
    · omega
  have hbound : w.length ≤ q * r := by
    rw [hrdef]
    have := le_smul_ceilDiv (a := q) (b := w.length) (by omega : (0:ℕ) < q)
    simpa using this
  obtain ⟨V, hmem, hcard, hprop⟩ :=
    suffix_segmentation_bound_by_chunk_vocabulary_aux r hr q (by omega) w hbound
  refine ⟨V, ?_, hcard, ?_⟩
  · intro u hu
    simpa only [word_substrings, Set.mem_setOf_eq] using hmem u hu
  · intro y hy
    rw [word_suffixes] at hy
    simp only [Set.mem_setOf_eq] at hy
    obtain ⟨hsuf, hyne⟩ := hy
    obtain ⟨p, hp⟩ := hsuf
    have hdrop : w.drop p.length = y := by
      rw [← hp, List.drop_append]
      simp
    obtain ⟨hb0, hb1⟩ := hprop p.length y hdrop hyne
    by_cases hm0 : p.length % r = 0
    · obtain ⟨tokens, hseg, hlen⟩ := hb0 hm0
      exact ⟨tokens, hseg, hlen.trans (chunk_token_bound_le M q hq hqM)⟩
    · obtain ⟨tokens, hseg, hlen⟩ := hb1 hm0
      refine ⟨tokens, hseg, ?_⟩
      have hreq : r - 1 = w.length ⌈/⌉ q - 1 := by rw [hrdef]
      rw [hreq] at hlen
      exact hlen.trans (chunk_inner_token_bound_le M q w.length hl)
