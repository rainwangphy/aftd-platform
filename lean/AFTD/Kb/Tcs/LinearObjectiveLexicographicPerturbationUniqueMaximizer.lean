import AFTD.Prelude

/-!
# linear_objective_lexicographic_perturbation_unique_maximizer

Topic: algorithms   Node: a269a567e11d

Provenance: formalization of a published result. Source: arXiv:2611.28757, Lemma 5.1

Lemma 5.1 of arXiv:2611.28757 (class-independent lexicographic perturbation). For every natural number L and every weight vector w : Fin L → ℝ there is a real δ > 0 (chosen before, hence independent of, the set K below) with the following properties, where the score of a word x : Fin L → Bool under weights v is ∑ i, v i * (if x i then 1 else 0) and the refined weights are w i - δ * (1/2)^(i+1) for the 0-based index i (the paper's w_i - δ 2^{-i}, i = 1..L). (a) Any two distinct words have different refined scores. (b) For every nonempty set K of words there is x in K such that: every y in K with y ≠ x has strictly smaller refined score than x (x is the unique maximizer of the refined objective over K); x maximizes the original w-score over K; and every y in K with y ≠ x that also maximizes the w-score over K is lexicographically larger than x, i.e. there is an index k with x j = y j for all j < k, x k = false and y k = true (so x is the lexicographically smallest w-maximizer, the paper's ERM_K(w)).
-/

theorem pr1640_kappa_bounds : ∀ (L : ℕ) (x : Fin L → Bool),
    0 ≤ ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0) ∧
    ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0) ≤ 1 - (1/2:ℝ)^L := by
  intro L
  induction L with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [Fin.sum_univ_castSucc]
    obtain ⟨h0, h1⟩ := ih (fun i => x (Fin.castSucc i))
    simp only [Fin.val_castSucc, Fin.val_last]
    have hp : (0:ℝ) < (1/2:ℝ)^n := by positivity
    have e : (1/2:ℝ)^(n+1) = (1/2:ℝ)^n / 2 := by rw [pow_succ]; ring
    constructor
    · split_ifs <;> linarith
    · split_ifs <;> linarith

theorem pr1640_kappa_lex : ∀ (L : ℕ) (x y : Fin L → Bool) (k : Fin L),
    (∀ j, j < k → x j = y j) → x k = false → y k = true →
    (1/2:ℝ)^L ≤ ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if y i then (1:ℝ) else 0)
      - ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0) := by
  intro L
  induction L with
  | zero => intro x y k; exact k.elim0
  | succ n ih =>
    intro x y k hlt hx hy
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have e : (1/2:ℝ)^(n+1) = (1/2:ℝ)^n / 2 := by rw [pow_succ]; ring
    have hp : (0:ℝ) < (1/2:ℝ)^n := by positivity
    induction k using Fin.lastCases with
    | last =>
      have hsum : ∑ i : Fin n, (1/2:ℝ)^(i.val+1) * (if y (Fin.castSucc i) then (1:ℝ) else 0)
          = ∑ i : Fin n, (1/2:ℝ)^(i.val+1) * (if x (Fin.castSucc i) then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hlt (Fin.castSucc i) (Fin.castSucc_lt_last i)]
      rw [hsum, hx, hy]
      simp
    | cast k' =>
      have := ih (fun i => x (Fin.castSucc i)) (fun i => y (Fin.castSucc i)) k'
        (fun j hj => hlt _ (Fin.castSucc_lt_castSucc_iff.mpr hj)) hx hy
      split_ifs <;> linarith

theorem pr1640_lex_total (L : ℕ) (x y : Fin L → Bool) (h : x ≠ y) :
    (∃ k, (∀ j, j < k → x j = y j) ∧ x k = false ∧ y k = true) ∨
    (∃ k, (∀ j, j < k → y j = x j) ∧ y k = false ∧ x k = true) := by
  have hS : (Finset.univ.filter (fun i => x i ≠ y i)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact ⟨i, by simp [hi]⟩
  have hk := Finset.min'_mem _ hS
  have hne : x ((Finset.univ.filter (fun i => x i ≠ y i)).min' hS) ≠ y ((Finset.univ.filter (fun i => x i ≠ y i)).min' hS) :=
    (Finset.mem_filter.mp hk).2
  have hlt : ∀ j, j < (Finset.univ.filter (fun i => x i ≠ y i)).min' hS → x j = y j := by
    intro j hj
    by_contra hc
    have : (Finset.univ.filter (fun i => x i ≠ y i)).min' hS ≤ j := Finset.min'_le _ j (by simp [hc])
    exact absurd hj (not_lt.mpr this)
  generalize (Finset.univ.filter (fun i => x i ≠ y i)).min' hS = k at hne hlt
  cases hxk : x k <;> cases hyk : y k
  · exact absurd (hxk.trans hyk.symm) hne
  · exact Or.inl ⟨k, hlt, hxk, hyk⟩
  · exact Or.inr ⟨k, fun j hj => (hlt j hj).symm, hyk, hxk⟩
  · exact absurd (hxk.trans hyk.symm) hne

theorem linear_objective_lexicographic_perturbation_unique_maximizer (L : ℕ) (w : Fin L → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x y : Fin L → Bool, x ≠ y →
        ∑ i, (w i - δ * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0)
          ≠ ∑ i, (w i - δ * (1/2:ℝ)^(i.val+1)) * (if y i then (1:ℝ) else 0)) ∧
      ∀ K : Set (Fin L → Bool), K.Nonempty → ∃ x ∈ K,
        (∀ y ∈ K, y ≠ x →
          ∑ i, (w i - δ * (1/2:ℝ)^(i.val+1)) * (if y i then (1:ℝ) else 0)
            < ∑ i, (w i - δ * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0)) ∧
        (∀ y ∈ K, ∑ i, w i * (if y i then (1:ℝ) else 0) ≤ ∑ i, w i * (if x i then (1:ℝ) else 0)) ∧
        (∀ y ∈ K, (∀ z ∈ K, ∑ i, w i * (if z i then (1:ℝ) else 0) ≤ ∑ i, w i * (if y i then (1:ℝ) else 0)) →
          y ≠ x → ∃ k, (∀ j, j < k → x j = y j) ∧ x k = false ∧ y k = true) := by
  classical
  obtain ⟨γ, hγ, hgap⟩ : ∃ γ : ℝ, 0 < γ ∧ ∀ x y : Fin L → Bool,
      ∑ i, w i * (if y i then (1:ℝ) else 0) < ∑ i, w i * (if x i then (1:ℝ) else 0) →
      γ ≤ ∑ i, w i * (if x i then (1:ℝ) else 0) - ∑ i, w i * (if y i then (1:ℝ) else 0) := by
    by_cases hD : ((Finset.univ.image (fun p : (Fin L → Bool) × (Fin L → Bool) =>
        ∑ i, w i * (if p.1 i then (1:ℝ) else 0) - ∑ i, w i * (if p.2 i then (1:ℝ) else 0))).filter (fun d => 0 < d)).Nonempty
    · refine ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ hD)).2, fun x y hxy => Finset.min'_le _ _ ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩, by linarith⟩
    · refine ⟨1, one_pos, fun x y hxy => absurd ⟨_, Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(x, y), Finset.mem_univ _, rfl⟩, by linarith⟩⟩ hD⟩
  refine ⟨γ / 2, by positivity, ?_⟩
  have hpert : ∀ x : Fin L → Bool, ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0)
      = ∑ i, w i * (if x i then (1:ℝ) else 0) - γ / 2 * ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0) := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hpL : (0:ℝ) < (1/2:ℝ)^L := by positivity
  have hA : ∀ x y : Fin L → Bool,
      ∑ i, w i * (if y i then (1:ℝ) else 0) < ∑ i, w i * (if x i then (1:ℝ) else 0) →
      ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if y i then (1:ℝ) else 0)
        < ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0) := by
    intro x y hxy
    rw [hpert, hpert]
    have h1 := hgap x y hxy
    obtain ⟨-, hx1⟩ := pr1640_kappa_bounds L x
    obtain ⟨hy0, -⟩ := pr1640_kappa_bounds L y
    have h2 : γ / 2 * ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0) ≤ γ / 2 * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 0 ≤ γ / 2 * ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if y i then (1:ℝ) else 0) :=
      mul_nonneg (by positivity) hy0
    linarith
  have hB : ∀ x y : Fin L → Bool,
      ∑ i, w i * (if x i then (1:ℝ) else 0) = ∑ i, w i * (if y i then (1:ℝ) else 0) →
      (∃ k, (∀ j, j < k → x j = y j) ∧ x k = false ∧ y k = true) →
      ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if y i then (1:ℝ) else 0)
        < ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0) := by
    rintro x y hxy ⟨k, hlt, hxk, hyk⟩
    rw [hpert, hpert, hxy]
    have h1 := pr1640_kappa_lex L x y k hlt hxk hyk
    have h2 : γ / 2 * ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if x i then (1:ℝ) else 0)
        < γ / 2 * ∑ i : Fin L, (1/2:ℝ)^(i.val+1) * (if y i then (1:ℝ) else 0) :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    linarith
  have hinj : ∀ x y : Fin L → Bool, x ≠ y →
      ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0)
        ≠ ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if y i then (1:ℝ) else 0) := by
    intro x y hne
    rcases lt_trichotomy (∑ i, w i * (if x i then (1:ℝ) else 0)) (∑ i, w i * (if y i then (1:ℝ) else 0)) with h | h | h
    · exact (hA y x h).ne
    · rcases pr1640_lex_total L x y hne with hl | hl
      · exact (hB x y h hl).ne'
      · exact (hB y x h.symm hl).ne
    · exact (hA x y h).ne'
  refine ⟨hinj, fun K hK => ?_⟩
  obtain ⟨x, hxK, hmax⟩ := Set.exists_max_image K
    (fun x => ∑ i, (w i - γ / 2 * (1/2:ℝ)^(i.val+1)) * (if x i then (1:ℝ) else 0)) (Set.toFinite K) hK
  have hwmax : ∀ y ∈ K, ∑ i, w i * (if y i then (1:ℝ) else 0) ≤ ∑ i, w i * (if x i then (1:ℝ) else 0) := by
    intro y hy
    by_contra hc
    exact absurd (hA y x (not_le.mp hc)) (not_lt.mpr (hmax y hy))
  refine ⟨x, hxK, fun y hy hne => lt_of_le_of_ne (hmax y hy) (hinj y x hne), hwmax, ?_⟩
  intro y hy hymax hne
  have heq := le_antisymm (hymax x hxK) (hwmax y hy)
  rcases pr1640_lex_total L x y (Ne.symm hne) with hl | hl
  · exact hl
  · exact absurd (hB y x heq.symm hl) (not_lt.mpr (hmax y hy))
