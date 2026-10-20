import AFTD.Prelude
import AFTD.Kb.Tcs.PosetUpset
import AFTD.Kb.Tcs.StandardExample
import AFTD.Kb.Tcs.PosetDownset
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.StandardExamplePartialOrder
import AFTD.Kb.Tcs.IsMinMaxIncompPair
import AFTD.Kb.Tcs.IsStandardExampleFree
import AFTD.Kb.Tcs.PosetHeightTwo
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# standard_example_reduction_min_max_subposet

Topic: combinatorics   Node: 46a9f6aeec8b

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 3.3, Lemma 3.5

Let P be a finite poset of height 2 and let (u, v) be a min-max incomparable pair in P. If d ≥ 3 and P is S_d-free, then the subposet induced by D_P(v) ∪ U_P(u) is S_{d-1}-free.
-/

lemma standard_example_reduction_min_max_subposet_subposet_lt_downset
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} {x y : {x : P // x ∈ poset_downset v ∪ poset_upset u}}
    (h : x.val < y.val) : x.val < v := by
  cases x.property with
  | inl hx => exact hx
  | inr hx =>
    exfalso
    exact hP u x.val y.val ⟨hx, h⟩

lemma standard_example_reduction_min_max_subposet_subposet_lt_upset
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} {x y : {x : P // x ∈ poset_downset v ∪ poset_upset u}}
    (h : x.val < y.val) : u < y.val := by
  cases y.property with
  | inl hy =>
    exfalso
    exact hP x.val y.val v ⟨h, hy⟩
  | inr hy => exact hy

lemma standard_example_reduction_min_max_subposet_min_lt_v
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} {k : ℕ} (hk : 2 ≤ k)
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u})
    (i : Fin k) : (f (StandardExample.min i)).val < v := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hj⟩ := exists_ne i
  have h_lt : StandardExample.min i < StandardExample.max j := by
    rw [lt_iff_le_and_ne]
    refine ⟨hj.symm, fun h => by cases h⟩
  have h_flt : f (StandardExample.min i) < f (StandardExample.max j) :=
    (OrderEmbedding.lt_iff_lt f).mpr h_lt
  exact standard_example_reduction_min_max_subposet_subposet_lt_downset hP (Subtype.coe_lt_coe.mpr h_flt)

lemma standard_example_reduction_min_max_subposet_u_lt_max
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} {k : ℕ} (hk : 2 ≤ k)
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u})
    (j : Fin k) : u < (f (StandardExample.max j)).val := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨i, hi⟩ := exists_ne j
  have h_lt : StandardExample.min i < StandardExample.max j := by
    rw [lt_iff_le_and_ne]
    refine ⟨hi, fun h => by cases h⟩
  have h_flt : f (StandardExample.min i) < f (StandardExample.max j) :=
    (OrderEmbedding.lt_iff_lt f).mpr h_lt
  exact standard_example_reduction_min_max_subposet_subposet_lt_upset hP (Subtype.coe_lt_coe.mpr h_flt)

lemma standard_example_reduction_min_max_subposet_not_u_le_min
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {x : P} (hx : x < v) : ¬ u ≤ x := by
  intro h
  rcases lt_or_eq_of_le h with hlt | heq
  · exact hP u x v ⟨hlt, hx⟩
  · subst heq
    exact h_uv.2.2.1 hx.le

lemma standard_example_reduction_min_max_subposet_not_min_le_u
    {P : Type*} [PartialOrder P]
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {x : P} (hx : x < v) : ¬ x ≤ u := by
  intro h
  have hu : u ≤ x := h_uv.1 h
  have heq : x = u := le_antisymm h hu
  subst heq
  exact h_uv.2.2.1 hx.le

lemma standard_example_reduction_min_max_subposet_not_max_le_v
    {P : Type*} [PartialOrder P] (hP : poset_height_two P)
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {y : P} (hy : u < y) : ¬ y ≤ v := by
  intro h
  rcases lt_or_eq_of_le h with hlt | heq
  · exact hP u y v ⟨hy, hlt⟩
  · subst heq
    exact h_uv.2.2.1 hy.le

lemma standard_example_reduction_min_max_subposet_not_v_le_max
    {P : Type*} [PartialOrder P]
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {y : P} (hy : u < y) : ¬ v ≤ y := by
  intro h
  have hv : y ≤ v := h_uv.2.1 h
  have heq : y = v := le_antisymm hv h
  subst heq
  exact h_uv.2.2.1 hy.le

def standard_example_reduction_min_max_subposet_embed_elem
    {P : Type*} [PartialOrder P] {u v : P} {k : ℕ}
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u}) :
    StandardExample (k + 1) → P
  | StandardExample.min i =>
    Fin.lastCases u (fun i' => (f (StandardExample.min i')).val) i
  | StandardExample.max j =>
    Fin.lastCases v (fun j' => (f (StandardExample.max j')).val) j

@[simp] lemma standard_example_reduction_min_max_subposet_embed_elem_min_last
    {P : Type*} [PartialOrder P] {u v : P} {k : ℕ}
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u}) :
    standard_example_reduction_min_max_subposet_embed_elem f (StandardExample.min (Fin.last k)) = u := by
  dsimp [standard_example_reduction_min_max_subposet_embed_elem]; rw [Fin.lastCases_last]

@[simp] lemma standard_example_reduction_min_max_subposet_embed_elem_min_cast
    {P : Type*} [PartialOrder P] {u v : P} {k : ℕ}
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u}) (i : Fin k) :
    standard_example_reduction_min_max_subposet_embed_elem f (StandardExample.min i.castSucc) =
      (f (StandardExample.min i)).val := by
  dsimp [standard_example_reduction_min_max_subposet_embed_elem]; rw [Fin.lastCases_castSucc]

@[simp] lemma standard_example_reduction_min_max_subposet_embed_elem_max_last
    {P : Type*} [PartialOrder P] {u v : P} {k : ℕ}
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u}) :
    standard_example_reduction_min_max_subposet_embed_elem f (StandardExample.max (Fin.last k)) = v := by
  dsimp [standard_example_reduction_min_max_subposet_embed_elem]; rw [Fin.lastCases_last]

@[simp] lemma standard_example_reduction_min_max_subposet_embed_elem_max_cast
    {P : Type*} [PartialOrder P] {u v : P} {k : ℕ}
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u}) (j : Fin k) :
    standard_example_reduction_min_max_subposet_embed_elem f (StandardExample.max j.castSucc) =
      (f (StandardExample.max j)).val := by
  dsimp [standard_example_reduction_min_max_subposet_embed_elem]; rw [Fin.lastCases_castSucc]

lemma standard_example_reduction_min_max_subposet_embed_elem_le_iff
    {P : Type*} [PartialOrder P]
    (hP : poset_height_two P)
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {k : ℕ} (hk : 2 ≤ k)
    (f : StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u})
    (a b : StandardExample (k + 1)) :
    standard_example_reduction_min_max_subposet_embed_elem f a ≤
      standard_example_reduction_min_max_subposet_embed_elem f b ↔ a ≤ b := by
  rcases a with i | j <;> rcases b with i' | j'
  · induction i using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_last]
        exact iff_of_true le_rfl rfl
      | cast i' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_last,
          standard_example_reduction_min_max_subposet_embed_elem_min_cast]
        exact iff_of_false (standard_example_reduction_min_max_subposet_not_u_le_min hP h_uv
          (standard_example_reduction_min_max_subposet_min_lt_v hP hk f i'))
          (Fin.castSucc_lt_last i').ne'
    | cast i =>
      induction i' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_last,
          standard_example_reduction_min_max_subposet_embed_elem_min_cast]
        exact iff_of_false (standard_example_reduction_min_max_subposet_not_min_le_u h_uv
          (standard_example_reduction_min_max_subposet_min_lt_v hP hk f i))
          (Fin.castSucc_lt_last i).ne
      | cast i' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_cast]
        rw [Subtype.coe_le_coe, OrderEmbedding.le_iff_le]
        exact Fin.castSucc_inj.symm
  · induction i using Fin.lastCases with
    | last =>
      induction j' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_last,
          standard_example_reduction_min_max_subposet_embed_elem_max_last]
        exact iff_of_false h_uv.2.2.1 (not_not.mpr rfl)
      | cast j' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_last,
          standard_example_reduction_min_max_subposet_embed_elem_max_cast]
        exact iff_of_true (standard_example_reduction_min_max_subposet_u_lt_max hP hk f j').le
          (Fin.castSucc_lt_last j').ne'
    | cast i =>
      induction j' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_cast,
          standard_example_reduction_min_max_subposet_embed_elem_max_last]
        exact iff_of_true (standard_example_reduction_min_max_subposet_min_lt_v hP hk f i).le
          (Fin.castSucc_lt_last i).ne
      | cast j' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_min_cast,
          standard_example_reduction_min_max_subposet_embed_elem_max_cast]
        rw [Subtype.coe_le_coe, OrderEmbedding.le_iff_le]
        exact Fin.castSucc_inj.ne.symm
  · induction j using Fin.lastCases with
    | last =>
      induction i' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_last,
          standard_example_reduction_min_max_subposet_embed_elem_min_last]
        exact iff_of_false h_uv.2.2.2 id
      | cast i' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_last,
          standard_example_reduction_min_max_subposet_embed_elem_min_cast]
        have hlt := standard_example_reduction_min_max_subposet_min_lt_v hP hk f i'
        exact iff_of_false (fun hle => lt_irrefl _ (lt_of_le_of_lt hle hlt)) id
    | cast j =>
      induction i' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_cast,
          standard_example_reduction_min_max_subposet_embed_elem_min_last]
        have hlt := standard_example_reduction_min_max_subposet_u_lt_max hP hk f j
        exact iff_of_false (fun hle => lt_irrefl _ (lt_of_lt_of_le hlt hle)) id
      | cast i' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_cast,
          standard_example_reduction_min_max_subposet_embed_elem_min_cast]
        rw [Subtype.coe_le_coe, OrderEmbedding.le_iff_le]
        rfl
  · induction j using Fin.lastCases with
    | last =>
      induction j' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_last]
        exact iff_of_true le_rfl rfl
      | cast j' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_last,
          standard_example_reduction_min_max_subposet_embed_elem_max_cast]
        exact iff_of_false (standard_example_reduction_min_max_subposet_not_v_le_max h_uv
          (standard_example_reduction_min_max_subposet_u_lt_max hP hk f j'))
          (Fin.castSucc_lt_last j').ne'
    | cast j =>
      induction j' using Fin.lastCases with
      | last =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_last,
          standard_example_reduction_min_max_subposet_embed_elem_max_cast]
        exact iff_of_false (standard_example_reduction_min_max_subposet_not_max_le_v hP h_uv
          (standard_example_reduction_min_max_subposet_u_lt_max hP hk f j))
          (Fin.castSucc_lt_last j).ne
      | cast j' =>
        simp only [standard_example_reduction_min_max_subposet_embed_elem_max_cast]
        rw [Subtype.coe_le_coe, OrderEmbedding.le_iff_le]
        exact Fin.castSucc_inj.symm

/-- Standard example reduction in min-max downset-upset subposets (Lemma 3.5). -/
theorem standard_example_reduction_min_max_subposet
    {P : Type*} [Fintype P] [PartialOrder P]
    (hP : poset_height_two P)
    {u v : P} (h_uv : is_min_max_incomp_pair u v)
    {d : ℕ} (hd : 3 ≤ d)
    (h_free : is_standard_example_free P d) :
    is_standard_example_free {x : P // x ∈ poset_downset v ∪ poset_upset u} (d - 1) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k ≥ 2, d = k + 1 := ⟨d - 1, by omega, (Nat.sub_add_cancel (by omega)).symm⟩
  change IsEmpty (StandardExample k ↪o {x : P // x ∈ poset_downset v ∪ poset_upset u})
  refine ⟨fun f => ?_⟩
  have g : StandardExample (k + 1) ↪o P :=
    OrderEmbedding.ofMapLEIff (standard_example_reduction_min_max_subposet_embed_elem f)
      (standard_example_reduction_min_max_subposet_embed_elem_le_iff hP h_uv hk f)
  exact h_free.false g
