import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteEnvyCycleImprovement
import AFTD.Kb.GameTheoryEconomics.FiniteUnenviedPermutation
import AFTD.Kb.GameTheoryEconomics.FiniteColumnSwitchImprovement

/-!
# finite_two_bonus_assignment

Topic: fair_division   Node: cbd380360d4d

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

For any finite nonempty real matrix w and two nonnegative agent-dependent bonus values g(false), g(true), there is a permutation of the old columns and an assignment of each bonus to one recipient which weakly improves every original diagonal, and for either bonus, removing that bonus from its recipient column leaves no foreign agent envying that column relative to her final utility. Recipients may coincide, and the Boolean records which bonus is assigned first.
-/

open Function Finset

theorem finite_two_bonus_assignment {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (w : α → α → ℝ) (g : Bool → α → ℝ) (hg : ∀ t i, 0 ≤ g t i) :
    ∃ (p : Equiv.Perm α) (r s : α) (t : Bool),
      (∀ i, w i i ≤ w i (p i) + (if i = r then g t i else 0) +
        (if i = s then g (!t) i else 0)) ∧
      (∀ i, i ≠ r → w i (p r) + (if r = s then g (!t) i else 0) ≤
        w i (p i) + (if i = r then g t i else 0) + (if i = s then g (!t) i else 0)) ∧
      (∀ i, i ≠ s → w i (p s) + (if s = r then g t i else 0) ≤
        w i (p i) + (if i = r then g t i else 0) + (if i = s then g (!t) i else 0)) := by
  classical
  let X := Equiv.Perm α × α × Bool
  let U (x : X) (i j : α) : ℝ := w i (x.1 j) + if j = x.2.1 then g x.2.2 i else 0
  let F (x : X) : Prop := (∀ i, w i i ≤ U x i i) ∧
    ∀ i, w i (x.1 x.2.1) ≤ U x i i
  let upd (x : X) (q : Equiv.Perm α) (t : Bool) : X :=
    ⟨q.trans x.1, q.symm x.2.1, t⟩
  have hbase (x : X) (q : Equiv.Perm α) (t : Bool) :
      (upd x q t).1 (upd x q t).2.1 = x.1 x.2.1 := by simp [upd]
  have hU (x : X) (q : Equiv.Perm α) (t : Bool) (i j : α) :
      U (upd x q t) i j = w i (x.1 (q j)) + if q j = x.2.1 then g t i else 0 := by
    have he : (j = q.symm x.2.1) ↔ q j = x.2.1 := by
      constructor
      · intro h
        rw [h, q.apply_symm_apply]
      · intro h
        rw [← h, q.symm_apply_apply]
    simp only [U, upd, Equiv.trans_apply, he]
  have hsU (x : X) (q : Equiv.Perm α) (i j : α) :
      U (upd x q x.2.2) i j = U x i (q j) := by rw [hU]
  have hcU (x : X) (q : Equiv.Perm α) (i : α) :
      U (upd x q (!x.2.2)) i i =
        if q i = x.2.1 then w i (x.1 x.2.1) + g (!x.2.2) i else U x i (q i) := by
    rw [hU]
    by_cases hi : q i = x.2.1 <;> simp [U, hi]
  have hF (x : X) (q : Equiv.Perm α) (t : Bool) (hx : F x)
      (hinc : ∀ i, U x i i ≤ U (upd x q t) i i) : F (upd x q t) := by
    refine ⟨fun i => (hx.1 i).trans (hinc i), ?_⟩
    intro i
    rw [hbase]
    exact (hx.2 i).trans (hinc i)
  let V (x : X) (s i : α) := U x i i + if i = s then g (!x.2.2) i else 0
  let C (x : X) (s : α) : Prop :=
    (∀ i, w i i ≤ V x s i) ∧
    (∀ i, i ≠ x.2.1 → w i (x.1 x.2.1) +
      (if x.2.1 = s then g (!x.2.2) i else 0) ≤ V x s i) ∧
    (∀ i, i ≠ s → w i (x.1 s) +
      (if s = x.2.1 then g x.2.2 i else 0) ≤ V x s i)
  have hV (x : X) (s i : α) : U x i i ≤ V x s i := by
    dsimp [V]
    apply le_add_of_nonneg_right
    split_ifs
    · exact hg _ _
    · exact le_rfl
  have hdistinct (x : X) (hx : F x) (s : α) (hs : s ≠ x.2.1)
      (hsource : ∀ i, U x i s ≤ U x i i) : C x s := by
    refine ⟨fun i => (hx.1 i).trans (hV x s i), ?_, ?_⟩
    · intro i hi
      simp only [if_neg hs.symm, add_zero]
      exact (hx.2 i).trans (hV x s i)
    · intro i hi
      simp only [if_neg hs, add_zero]
      have he : U x i s = w i (x.1 s) := by simp [U, hs]
      rw [← he]
      exact (hsource i).trans (hV x s i)
  have hsame (x : X) (hx : F x) (hsource : ∀ i, U x i x.2.1 ≤ U x i i)
      (hnew : ∀ i, i ≠ x.2.1 → w i (x.1 x.2.1) + g (!x.2.2) i ≤ U x i i) :
      C x x.2.1 := by
    refine ⟨fun i => (hx.1 i).trans (hV x x.2.1 i), ?_, ?_⟩
    · intro i hi
      simp only [ite_true]
      exact (hnew i hi).trans (hV x x.2.1 i)
    · intro i hi
      simp only [ite_true]
      have he : U x i x.2.1 = w i (x.1 x.2.1) + g x.2.2 i := by simp [U]
      rw [← he]
      exact (hsource i).trans (hV x x.2.1 i)
  suffices hex : ∃ (x : X) (s : α), C x s by
    obtain ⟨x, s, hx⟩ := hex
    exact ⟨x.1, x.2.1, s, x.2.2, hx⟩
  by_contra hnone
  have hn (x : X) (s : α) : ¬ C x s := fun h => hnone ⟨x, s, h⟩
  let S : Finset X := Finset.univ.filter F
  have hS : S.Nonempty := by
    obtain ⟨p, hp, s, hs⟩ := finite_unenvied_permutation w
    let x : X := ⟨p, s, false⟩
    have hge (i : α) : w i (p i) ≤ U x i i := by
      dsimp [U, x]
      apply le_add_of_nonneg_right
      split_ifs
      · exact hg _ _
      · exact le_rfl
    have hx : F x := ⟨fun i => (hp i).trans (hge i), fun i => (hs i).trans (hge i)⟩
    exact ⟨x, by simp [S, hx]⟩
  obtain ⟨x, hxS, hmax⟩ := Finset.exists_max_image S (fun x => ∑ i, U x i i) hS
  have hx : F x := (Finset.mem_filter.mp hxS).2
  have noimp (q : Equiv.Perm α) (t : Bool)
      (hinc : ∀ i, U x i i ≤ U (upd x q t) i i)
      (hlt : ∃ i, U x i i < U (upd x q t) i i) : False := by
    have hy := hF x q t hx hinc
    have htot : (∑ i, U x i i) < ∑ i, U (upd x q t) i i :=
      Finset.sum_lt_sum (fun i _ => hinc i) (by obtain ⟨i, hi⟩ := hlt; exact ⟨i, Finset.mem_univ _, hi⟩)
    exact (not_lt_of_ge (hmax _ (by simp [S, hy]))) htot
  have noold (q : Equiv.Perm α) (hinc : ∀ i, U x i i ≤ U x i (q i))
      (hlt : ∃ i, U x i i < U x i (q i)) : False := by
    apply noimp q x.2.2
    · simpa only [hsU] using hinc
    · simpa only [hsU] using hlt
  have hother (j : α) (hj : j ≠ x.2.1) : ∃ i, U x i i < U x i j := by
    by_contra h
    push Not at h
    exact hn x j (hdistinct x hx j hj h)
  have hsource : ∀ i, U x i x.2.1 ≤ U x i i := by
    by_contra h
    push Not at h
    have hall (j : α) : ∃ i, U x i i < U x i j := by
      by_cases hj : j = x.2.1
      · simpa only [hj] using h
      · exact hother j hj
    obtain ⟨q, hq, i, hi⟩ := finite_envy_cycle_improvement (U x) hall
    exact noold q hq ⟨i, hi⟩
  have hnew : ∃ i, i ≠ x.2.1 ∧ U x i i < w i (x.1 x.2.1) + g (!x.2.2) i := by
    by_contra h
    push Not at h
    exact hn x x.2.1 (hsame x hx hsource h)
  obtain hold | hswap := finite_column_switch_improvement (U x) x.2.1
    (fun i => w i (x.1 x.2.1) + g (!x.2.2) i) hother hnew
  · obtain ⟨q, hq, i, hi⟩ := hold
    exact noold q hq ⟨i, hi⟩
  · obtain ⟨q, hq, i, hi⟩ := hswap
    apply noimp q (!x.2.2)
    · simpa only [hcU] using hq
    · exact ⟨i, by simpa only [hcU] using hi⟩
