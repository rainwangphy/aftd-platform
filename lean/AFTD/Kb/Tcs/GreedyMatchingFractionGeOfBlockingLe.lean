import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentBlockingBoundLe
import AFTD.Kb.Tcs.IsHereditarySegmentProperty
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.GreedyMatching
import AFTD.Kb.Tcs.SegmentEndpoints
import AFTD.Kb.Tcs.GreedyStep
import AFTD.Kb.Tcs.SegmentsBlockPointsProp
import AFTD.Kb.Tcs.GreedyMatchingNil
import AFTD.Kb.Tcs.G

/-!
# greedy_matching_fraction_ge_of_blocking_le

Topic: online_algorithms   Node: 89dcd201f1dd

Provenance: formalization of a published result. Source: arXiv:2610.23130 Theorem 1.2 (1)

Let P be a hereditary segment property. If β_P(ℓ) ≤ p (formalized by segment_blocking_bound_le P ℓ p), then on every duplicate-free list pts of points in ℝ² in general position on which Greedy creates ℓ segments, Greedy matches at least a 2ℓ / (2ℓ + p) fraction of the input points, meaning (2ℓ)/(2ℓ+p) ≤ 2ℓ / pts.length.
-/

def greedy_matching_fraction_ge_of_blocking_le_inv (P : Finset (Sym2 (ℝ × ℝ)) → Prop)
    (w : List (ℝ × ℝ)) (M : Finset (Sym2 (ℝ × ℝ))) (U : List (ℝ × ℝ)) : Prop :=
  P M ∧ segments_block_points_prop P M U.toFinset ∧ U.Nodup ∧
    segment_endpoints M ∪ U.toFinset = w.toFinset

lemma greedy_matching_fraction_ge_of_blocking_le_endpoints_insert_pair
    (u v : ℝ × ℝ) (M : Finset (Sym2 (ℝ × ℝ))) :
    segment_endpoints (insert s(u, v) M) = {u, v} ∪ segment_endpoints M := by
  simp [segment_endpoints, Finset.biUnion_insert]

lemma greedy_matching_fraction_ge_of_blocking_le_endpoints_card_le
    (L : Finset (Sym2 (ℝ × ℝ))) : (segment_endpoints L).card ≤ 2 * L.card := by
  classical
  induction L using Finset.induction_on with
  | empty => simp [segment_endpoints]
  | insert a L ha ih =>
    induction a using Sym2.ind with
    | _ u v =>
      rw [greedy_matching_fraction_ge_of_blocking_le_endpoints_insert_pair]
      calc (({u, v} : Finset (ℝ × ℝ)) ∪ segment_endpoints L).card
          ≤ ({u, v} : Finset (ℝ × ℝ)).card + (segment_endpoints L).card :=
              Finset.card_union_le _ _
        _ ≤ 2 + 2 * L.card := Nat.add_le_add Finset.card_le_two ih
        _ = 2 * (insert s(u, v) L).card := by
              rw [Finset.card_insert_of_notMem ha]; ring

lemma greedy_matching_fraction_ge_of_blocking_le_not_mem_erase_self
    (l : List (ℝ × ℝ)) (h : l.Nodup) (a : ℝ × ℝ) : a ∉ l.erase a := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hbt, ht⟩ := h
    by_cases hba : b = a
    · subst hba
      rw [List.erase_cons_head]
      exact hbt
    · rw [List.erase_cons]
      simp only [beq_iff_eq]
      rw [if_neg hba]
      simp only [List.mem_cons, not_or]
      exact ⟨fun hab => hba hab.symm, ih ht⟩

lemma greedy_matching_fraction_ge_of_blocking_le_mem_erase_toFinset
    (l : List (ℝ × ℝ)) (h : l.Nodup) (a x : ℝ × ℝ) :
    x ∈ (l.erase a).toFinset ↔ x ∈ l.toFinset ∧ x ≠ a := by
  simp only [List.mem_toFinset]
  constructor
  · intro hx
    refine ⟨List.mem_of_mem_erase (a := x) (b := a) (l := l) hx, ?_⟩
    rintro rfl
    exact greedy_matching_fraction_ge_of_blocking_le_not_mem_erase_self l h x hx
  · rintro ⟨hx, hne⟩
    exact (List.mem_erase_of_ne (a := x) (b := a) (l := l) hne).mpr hx

lemma greedy_matching_fraction_ge_of_blocking_le_insert_erase_toFinset
    (l : List (ℝ × ℝ)) (h : l.Nodup) (a : ℝ × ℝ) (ha : a ∈ l) :
    insert a (l.erase a).toFinset = l.toFinset := by
  ext x
  simp only [Finset.mem_insert, List.mem_toFinset,
    greedy_matching_fraction_ge_of_blocking_le_mem_erase_toFinset l h a x]
  constructor
  · rintro (rfl | ⟨hx, _⟩)
    · exact ha
    · exact hx
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr ⟨hx, hxa⟩

lemma greedy_matching_fraction_ge_of_blocking_le_some_union
    (E Ke W : Finset (ℝ × ℝ)) (u a : ℝ × ℝ) (hE : E ∪ insert u Ke = W) :
    ({u, a} : Finset (ℝ × ℝ)) ∪ E ∪ Ke = W ∪ {a} := by
  rw [← hE]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma greedy_matching_fraction_ge_of_blocking_le_step
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P)
    (w : List (ℝ × ℝ)) (M : Finset (Sym2 (ℝ × ℝ))) (U : List (ℝ × ℝ)) (a : ℝ × ℝ)
    (hinv : greedy_matching_fraction_ge_of_blocking_le_inv P w M U)
    (ha : a ∉ w.toFinset) :
    greedy_matching_fraction_ge_of_blocking_le_inv P (w ++ [a])
      (greedyStep P (M, U) a).1 (greedyStep P (M, U) a).2 := by
  obtain ⟨hPM, hblk, hUnd, heq⟩ := hinv
  classical
  let g : ℝ × ℝ → Bool := fun u => decide (P (insert s(u, a) M))
  have hgd : greedyStep P (M, U) a = (match List.find? g U with
      | some u => (insert s(u, a) M, U.erase u)
      | none => (M, U ++ [a])) := rfl
  rw [hgd]
  cases hf : List.find? g U with
  | some u =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact of_decide_eq_true (by simpa [g] using List.find?_some hf)
      · intro x y hx hy hxy hbig
        obtain ⟨hxU, hxu⟩ :=
          (greedy_matching_fraction_ge_of_blocking_le_mem_erase_toFinset U hUnd u x).mp hx
        obtain ⟨hyU, hyu⟩ :=
          (greedy_matching_fraction_ge_of_blocking_le_mem_erase_toFinset U hUnd u y).mp hy
        exact hblk hxU hyU hxy
          (hP.2 (Finset.insert_subset_insert s(x, y) (Finset.subset_insert s(u, a) M)) hbig)
      · exact List.Nodup.erase u hUnd
      · rw [greedy_matching_fraction_ge_of_blocking_le_endpoints_insert_pair]
        have hu : u ∈ U := List.mem_of_find?_eq_some hf
        have hUins : insert u (U.erase u).toFinset = U.toFinset :=
          greedy_matching_fraction_ge_of_blocking_le_insert_erase_toFinset U hUnd u hu
        have hE : segment_endpoints M ∪ insert u (U.erase u).toFinset = w.toFinset := by
          rw [hUins]; exact heq
        rw [greedy_matching_fraction_ge_of_blocking_le_some_union
          (segment_endpoints M) (U.erase u).toFinset w.toFinset u a hE]
        rw [List.toFinset_append]
        simp
  | none =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hPM
      · intro x y hx hy hxy
        have hxn : x ∈ U.toFinset ∨ x = a := by
          rcases (by simpa using hx : x = a ∨ x ∈ U.toFinset) with h | h
          · exact Or.inr h
          · exact Or.inl h
        have hyn : y ∈ U.toFinset ∨ y = a := by
          rcases (by simpa using hy : y = a ∨ y ∈ U.toFinset) with h | h
          · exact Or.inr h
          · exact Or.inl h
        have hg : ∀ z ∈ U.toFinset, ¬ P (insert s(z, a) M) := by
          intro z hz
          have hzf : g z = false := by
            have h1 : ¬ g z = true := (List.find?_eq_none.mp hf) z (List.mem_toFinset.mp hz)
            exact Bool.eq_false_iff.mpr h1
          exact of_decide_eq_false (by simpa [g] using hzf)
        rcases hxn with hxU | rfl
        · rcases hyn with hyU | rfl
          · exact hblk hxU hyU hxy
          · exact hg x hxU
        · rcases hyn with hyU | rfl
          · have h1 := hg y hyU
            rwa [Sym2.eq_swap] at h1
          · exact absurd rfl hxy
      · have hUsub : U.toFinset ⊆ w.toFinset := by
          rw [← heq]; exact Finset.subset_union_right
        have haUf : a ∉ U.toFinset := fun h => ha (hUsub h)
        have haU : a ∉ U := fun h => haUf (List.mem_toFinset.mpr h)
        rw [List.nodup_append]
        refine ⟨hUnd, List.nodup_singleton a, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        exact fun hxa => haU (hxa ▸ hx)
      · rw [List.toFinset_append, ← Finset.union_assoc, heq]
        simp [List.toFinset_append]

lemma greedy_matching_fraction_ge_of_blocking_le_inv_nodup
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P)
    (pts : List (ℝ × ℝ)) (h : pts.Nodup) :
    greedy_matching_fraction_ge_of_blocking_le_inv P pts
      (greedyMatching P pts).1 (greedyMatching P pts).2 := by
  classical
  induction pts using List.reverseRecOn with
  | nil =>
    rw [greedyMatching_nil]
    refine ⟨hP.1, ?_, ?_, ?_⟩
    · intro u v hu hv huv
      simp at hu
    · simp
    · simp [segment_endpoints]
  | append_singleton w a ih =>
    obtain ⟨hw, _, hdisj⟩ := List.nodup_append.mp h
    have ha : a ∉ w.toFinset := by
      intro haw
      exact (hdisj a (List.mem_toFinset.mp haw) a (by simp)) rfl
    have hgm : greedyMatching P (w ++ [a]) = greedyStep P (greedyMatching P w) a := by
      simp [greedyMatching, List.foldl_append]
    rw [hgm]
    have hstep := greedy_matching_fraction_ge_of_blocking_le_step P hP w
      (greedyMatching P w).1 (greedyMatching P w).2 a (ih hw) ha
    rw [Prod.mk.eta] at hstep
    exact hstep

/-- Part (1) of Theorem 1.2: if β_P(ℓ) ≤ p, Greedy matches at least a 2ℓ/(2ℓ+p) fraction on every input producing ℓ segments. -/
theorem greedy_matching_fraction_ge_of_blocking_le
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P) (ℓ p : ℕ)
    (hβ : segment_blocking_bound_le P ℓ p) (pts : List (ℝ × ℝ))
    (h_nodup : pts.Nodup) (h_gen : points_in_general_position (pts.toFinset : Set (ℝ × ℝ)))
    (h_card : (greedyMatching P pts).1.card = ℓ) :
    (2 * (ℓ : ℝ)) / (2 * (ℓ : ℝ) + (p : ℝ)) ≤ (2 * (ℓ : ℝ)) / (pts.length : ℝ) := by
  classical
  obtain ⟨hPM, hblk, hUnd, heq⟩ :=
    greedy_matching_fraction_ge_of_blocking_le_inv_nodup P hP pts h_nodup
  have hgen' : points_in_general_position
      ((↑(segment_endpoints (greedyMatching P pts).1) : Set (ℝ × ℝ)) ∪
        (↑(greedyMatching P pts).2.toFinset : Set (ℝ × ℝ))) := by
    rw [← Finset.coe_union, heq]
    exact h_gen
  have hUcard : (greedyMatching P pts).2.toFinset.card ≤ p :=
    hβ (greedyMatching P pts).1 (greedyMatching P pts).2.toFinset h_card hPM hgen' hblk
  have hends : (segment_endpoints (greedyMatching P pts).1).card ≤ 2 * ℓ := by
    have h := greedy_matching_fraction_ge_of_blocking_le_endpoints_card_le
      (greedyMatching P pts).1
    rwa [h_card] at h
  have hlen : pts.length ≤ 2 * ℓ + p := by
    rw [← List.toFinset_card_of_nodup h_nodup]
    calc pts.toFinset.card
        = (segment_endpoints (greedyMatching P pts).1 ∪
            (greedyMatching P pts).2.toFinset).card := by rw [heq]
      _ ≤ (segment_endpoints (greedyMatching P pts).1).card +
            (greedyMatching P pts).2.toFinset.card := Finset.card_union_le _ _
      _ ≤ 2 * ℓ + p := Nat.add_le_add hends hUcard
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
  · subst hℓ0
    simp
  · have hnpos : 0 < pts.length := by
      rcases Nat.eq_zero_or_pos pts.length with h0 | hpos
      · exfalso
        have hnil : pts = [] := List.length_eq_zero_iff.mp h0
        subst hnil
        rw [greedyMatching_nil] at h_card
        simp at h_card
        omega
      · exact hpos
    have hden : (0 : ℝ) < (pts.length : ℝ) := by exact_mod_cast hnpos
    have hle : (pts.length : ℝ) ≤ 2 * (ℓ : ℝ) + (p : ℝ) := by exact_mod_cast hlen
    exact div_le_div_of_nonneg_left (by positivity) hden hle
