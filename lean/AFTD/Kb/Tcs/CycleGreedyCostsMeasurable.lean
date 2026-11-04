import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyCosts

/-!
# cycle_greedy_costs_measurable

Topic: online_algorithms   Node: f1c38a49b047

Provenance: helper lemma. Measurability of the process used in OP-894.

For every n, the vector of sequential nearest-free greedy costs is a Borel measurable function of the arrival vector.
-/

theorem cgcm_piecewise {X T Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [Finite T]
    {s : X → T} (hs : ∀ t, MeasurableSet {x | s x = t}) {h : T → X → Y}
    (hh : ∀ t, Measurable (h t)) : Measurable fun x => h (s x) x := by
  let _ : MeasurableSpace T := ⊤
  have : MeasurableSingletonClass T := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hsm : Measurable s := measurable_to_countable' fun t => hs t
  exact (measurable_from_prod_countable_left (f := fun p : X × T => h p.2 p.1) hh).comp
    (measurable_id.prodMk hsm)

noncomputable def cgcm_pick {n : ℕ} (free : Finset (Fin n)) (h : free.Nonempty)
    (f : Fin n → ℝ) : Fin n :=
  (free.filter (fun j => f j = (free.image f).min' (Finset.Nonempty.image h _))).min' (by
      have hmem := Finset.min'_mem (free.image f) (Finset.Nonempty.image h _)
      rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq⟩⟩)

theorem cgcm_pick_eq_iff {n : ℕ} (free : Finset (Fin n)) (h : free.Nonempty)
    (f : Fin n → ℝ) (j : Fin n) :
    cgcm_pick free h f = j ↔ j ∈ free ∧ ∀ j' ∈ free, f j < f j' ∨ (f j = f j' ∧ j ≤ j') := by
  unfold cgcm_pick
  set m := (free.image f).min' (Finset.Nonempty.image h _) with hm
  constructor
  · intro hj
    have hmem := Finset.min'_mem (free.filter (fun j => f j = m)) (by
      have hmem := Finset.min'_mem (free.image f) (Finset.Nonempty.image h _)
      rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq⟩⟩)
    rw [hj] at hmem
    obtain ⟨hjf, hjm⟩ := Finset.mem_filter.mp hmem
    refine ⟨hjf, fun j' hj' => ?_⟩
    have hle : m ≤ f j' := Finset.min'_le _ _ (Finset.mem_image_of_mem f hj')
    rcases lt_or_eq_of_le hle with hlt | heq
    · left; rw [hjm]; exact hlt
    · right
      refine ⟨by rw [hjm, heq], ?_⟩
      rw [← hj]
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', heq.symm⟩)
  · rintro ⟨hjf, hall⟩
    have hjm : f j = m := by
      apply le_antisymm
      · have hmem := Finset.min'_mem (free.image f) (Finset.Nonempty.image h _)
        rcases Finset.mem_image.mp hmem with ⟨j0, hj0, heq⟩
        rw [← hm] at heq
        rw [← heq]
        rcases hall j0 hj0 with hlt | ⟨heq', _⟩
        · exact hlt.le
        · exact heq'.le
      · exact Finset.min'_le _ _ (Finset.mem_image_of_mem f hjf)
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hjf, hjm⟩)
    · apply Finset.le_min'
      intro y hy
      obtain ⟨hyf, hym⟩ := Finset.mem_filter.mp hy
      rcases hall y hyf with hlt | ⟨_, hle⟩
      · rw [hjm, hym] at hlt; exact absurd hlt (lt_irrefl _)
      · exact hle

theorem cgcm_pick_measurable {n : ℕ} (free : Finset (Fin n)) (h : free.Nonempty)
    (D : ℝ → Fin n → ℝ) (hD : ∀ j, Measurable fun a => D a j) :
    Measurable fun a => cgcm_pick free h (D a) := by
  apply measurable_to_countable'
  intro j
  change MeasurableSet {a | cgcm_pick free h (D a) = j}
  simp only [cgcm_pick_eq_iff]
  by_cases hj : j ∈ free
  · simp only [hj, true_and]
    have : {a | ∀ j' ∈ free, D a j < D a j' ∨ (D a j = D a j' ∧ j ≤ j')} =
        ⋂ j' : Fin n, {a | j' ∈ free → D a j < D a j' ∨ (D a j = D a j' ∧ j ≤ j')} := by
      ext a; simp
    rw [this]
    refine MeasurableSet.iInter fun j' => ?_
    by_cases hj' : j' ∈ free
    · simp only [hj', true_implies]
      by_cases hle : j ≤ j'
      · simp only [hle, and_true]
        exact (measurableSet_lt (hD j) (hD j')).union (measurableSet_eq_fun (hD j) (hD j'))
      · simp only [hle, and_false, or_false]
        exact measurableSet_lt (hD j) (hD j')
    · simp [hj']
  · simp [hj]

theorem cycle_greedy_costs_measurable (n : ℕ) : Measurable (cycle_greedy_costs n) := by
  let D : ℝ → Fin n → ℝ := fun a j =>
    if n = 0 then 0
    else
      let d := a - (j.val : ℝ)
      let k : ℝ := ((⌊d / (n : ℝ) + 1 / 2⌋ : ℤ) : ℝ)
      |d - (n : ℝ) * k|
  let ST : Finset (Fin n) → ℝ → ℝ × Finset (Fin n) := fun τ a =>
    if h : τ.Nonempty then (D a (cgcm_pick τ h (D a)), τ.erase (cgcm_pick τ h (D a)))
    else (0, τ)
  let G : (Fin n → ℝ) → (List ℝ × Finset (Fin n)) → Fin n → (List ℝ × Finset (Fin n)) :=
    fun x acc i => (acc.1 ++ [(ST acc.2 (x i)).1], (ST acc.2 (x i)).2)
  have hdef : cycle_greedy_costs n =
      fun x i => ((List.finRange n).foldl (G x) ([], Finset.univ)).1.getD i.val 0 := rfl
  have hD : ∀ j, Measurable fun a => D a j := by
    intro j
    by_cases hn : n = 0
    · simp only [D, hn, if_true]; exact measurable_const
    · simp only [D, hn, if_false]
      have h1 : Measurable fun a : ℝ => ((⌊(a - (j.val : ℝ)) / (n : ℝ) + 1 / 2⌋ : ℤ) : ℝ) :=
        (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
          (((measurable_id.sub_const _).div_const _).add_const _).floor
      exact continuous_abs.measurable.comp ((measurable_id.sub_const _).sub (h1.const_mul _))
  have hfib : ∀ (F : (Fin n → ℝ) → List ℝ × Finset (Fin n)) (i : Fin n),
      (∀ σ, MeasurableSet {x | (F x).2 = σ}) →
      ∀ σ, MeasurableSet {x | (G x (F x) i).2 = σ} := by
    intro F i hF σ
    apply measurableSet_setOfPred.mpr
    refine cgcm_piecewise (s := fun x => (F x).2) hF
      (h := fun τ x => (ST τ (x i)).2 = σ) (fun τ => ?_)
    by_cases hτ : τ.Nonempty
    · simp only [ST, dif_pos hτ]
      exact (measurable_of_finite (fun j : Fin n => τ.erase j = σ)).comp
        ((cgcm_pick_measurable τ hτ D hD).comp (measurable_pi_apply i))
    · simp only [ST, dif_neg hτ]
      exact measurable_const
  have hcost : ∀ (F : (Fin n → ℝ) → List ℝ × Finset (Fin n)) (i : Fin n),
      (∀ σ, MeasurableSet {x | (F x).2 = σ}) →
      Measurable fun x => (ST (F x).2 (x i)).1 := by
    intro F i hF
    refine cgcm_piecewise (s := fun x => (F x).2) hF
      (h := fun τ x => (ST τ (x i)).1) (fun τ => ?_)
    by_cases hτ : τ.Nonempty
    · simp only [ST, dif_pos hτ]
      have hp := (cgcm_pick_measurable τ hτ D hD).comp (measurable_pi_apply (X := fun _ : Fin n => ℝ) i)
      exact cgcm_piecewise (s := fun x : Fin n → ℝ => cgcm_pick τ hτ (D (x i)))
        (fun t => hp (measurableSet_singleton t))
        (h := fun j x => D (x i) j) (fun j => (hD j).comp (measurable_pi_apply i))
    · simp only [ST, dif_neg hτ]
      exact measurable_const
  have key : ∀ (L : List (Fin n)) (F : (Fin n → ℝ) → List ℝ × Finset (Fin n)),
      (∀ σ, MeasurableSet {x | (F x).2 = σ}) →
      (∀ j, Measurable fun x => (F x).1.getD j 0) →
      (∀ x y, (F x).1.length = (F y).1.length) →
      ∀ j, Measurable fun x => (L.foldl (G x) (F x)).1.getD j 0 := by
    intro L
    induction L with
    | nil => intro F _ hget _ j; exact hget j
    | cons i L ih =>
      intro F hF hget hlen
      simp only [List.foldl_cons]
      apply ih (fun x => G x (F x) i) (hfib F i hF)
      · intro j
        let m := (F 0).1.length
        have hc := hcost F i hF
        have heq : ∀ x, (G x (F x) i).1.getD j 0 =
            if j < m then (F x).1.getD j 0 else if j = m then (ST (F x).2 (x i)).1 else 0 := by
          intro x
          have hl : (F x).1.length = m := hlen x 0
          simp only [G]
          split_ifs with h1 h2
          · rw [List.getD_append _ _ _ _ (by omega)]
          · rw [List.getD_append_right _ _ _ _ (by omega)]
            simp [h2, hl]
          · rw [List.getD_append_right _ _ _ _ (by omega)]
            have : j - (F x).1.length ≠ 0 := by omega
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
            simp [hk]
        simp only [heq]
        split_ifs
        · exact hget j
        · exact hc
        · exact measurable_const
      · intro x y
        simp [G, hlen x y]
  rw [hdef]
  exact measurable_pi_lambda _ fun i =>
    key (List.finRange n) (fun _ => ([], Finset.univ)) (fun σ => MeasurableSet.const _)
      (fun j => measurable_const) (fun _ _ => rfl) i.val
