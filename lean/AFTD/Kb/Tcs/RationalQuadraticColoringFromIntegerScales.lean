import AFTD.Prelude

/-!
# rational_quadratic_coloring_from_integer_scales

Topic: combinatorics   Node: cd38e4e2654b

Provenance: helper lemma. Compactness reduction for the rational quadratic approach to OP-1482.

If for every positive integer q there is an integer coloring avoiding false length-3 and true length-17 quadratics with leading coefficient q and arbitrary integer lower coefficients, then a rational coloring avoids those two types with leading coefficient one and arbitrary rational lower coefficients.
-/

private lemma rational_quadratic_coloring_from_integer_scales_rat_num_mul_eq_of_den_dvd (q : ℕ) (a : ℚ) (h : a.den ∣ q) :
    (((q / a.den : ℕ) : ℤ) * a.num : ℚ) = (q : ℚ) * a := by
  have hq : (q : ℚ) = (a.den : ℚ) * ((q / a.den : ℕ) : ℚ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
  calc
    (((q / a.den : ℕ) : ℤ) * a.num : ℚ)
        = ((q / a.den : ℕ) : ℚ) * (a.num : ℚ) := by
          simp only [Int.cast_natCast]
    _ = ((q / a.den : ℕ) : ℚ) * (a * (a.den : ℚ)) := by rw [← Rat.mul_den_eq_num a]
    _ = (((q / a.den : ℕ) : ℚ) * (a.den : ℚ)) * a := by ring
    _ = (q : ℚ) * a := by
          rw [mul_comm ((q / a.den : ℕ) : ℚ) (a.den : ℚ), ← hq]

private lemma rational_quadratic_coloring_from_integer_scales_rat_num_mul_int_quadratic
    (q : ℕ) (a b : ℚ) (A B : ℤ)
    (hA : (A : ℚ) = (q : ℚ) * a) (hB : (B : ℚ) = (q : ℚ) * b)
    (n : ℕ) (k : Fin n) :
    ((q : ℚ) * ((k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b)).num =
      (q : ℤ) * (k.val : ℤ) ^ 2 + A * (k.val : ℤ) + B := by
  let J : ℤ := (q : ℤ) * (k.val : ℤ) ^ 2 + A * (k.val : ℤ) + B
  have hq : (q : ℚ) * ((k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b) = (J : ℚ) := by
    dsimp [J]
    push_cast
    rw [hA, hB]
    ring
  have hnum := congrArg Rat.num hq
  simpa [Rat.num_intCast] using hnum

private lemma rational_quadratic_coloring_from_integer_scales_quadratic_coloring_constraint
    (q : ℕ) (f : ℤ → Bool) {n : ℕ} (target : Bool)
    (hf : ∀ A B : ℤ, ¬ ∀ k : Fin n,
      f ((q : ℤ) * (k.val : ℤ) ^ 2 + A * (k.val : ℤ) + B) = target)
    (a b : ℚ) (ha : a.den ∣ q) (hb : b.den ∣ q)
    (F : ℚ → Bool) (hF : ∀ x, F x = f ((q : ℚ) * x).num) :
    ¬ ∀ k : Fin n, F ((k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b) = target := by
  let A : ℤ := ((q / a.den : ℕ) : ℤ) * a.num
  let B : ℤ := ((q / b.den : ℕ) : ℤ) * b.num
  have hA : (A : ℚ) = (q : ℚ) * a := by
    dsimp [A]
    simp only [Int.cast_mul]
    exact rational_quadratic_coloring_from_integer_scales_rat_num_mul_eq_of_den_dvd q a ha
  have hB : (B : ℚ) = (q : ℚ) * b := by
    dsimp [B]
    simp only [Int.cast_mul]
    exact rational_quadratic_coloring_from_integer_scales_rat_num_mul_eq_of_den_dvd q b hb
  intro h
  apply hf A B
  intro k
  have hp := rational_quadratic_coloring_from_integer_scales_rat_num_mul_int_quadratic q a b A B hA hB n k
  have hk := h k
  rw [hF ((k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b), hp] at hk
  exact hk

theorem rational_quadratic_coloring_from_integer_scales (h : ∀ q : ℕ, 0 < q → ∃ f : ℤ → Bool, (∀ a b : ℤ, ¬ ∀ k : Fin 3, f ((q : ℤ) * (k.val : ℤ) ^ 2 + a * k.val + b) = false) ∧ (∀ a b : ℤ, ¬ ∀ k : Fin 17, f ((q : ℤ) * (k.val : ℤ) ^ 2 + a * k.val + b) = true)) : ∃ f : ℚ → Bool, (∀ a b : ℚ, ¬ ∀ k : Fin 3, f ((k.val : ℚ) ^ 2 + a * k.val + b) = false) ∧ (∀ a b : ℚ, ¬ ∀ k : Fin 17, f ((k.val : ℚ) ^ 2 + a * k.val + b) = true) := by
  let Index : Type := (ℚ × ℚ) ⊕ (ℚ × ℚ)
  let aa : Index → ℚ := fun i => match i with | Sum.inl p => p.1 | Sum.inr p => p.1
  let bb : Index → ℚ := fun i => match i with | Sum.inl p => p.2 | Sum.inr p => p.2
  let T : Index → Set (ℚ → Bool) := fun i =>
    match i with
    | Sum.inl p => {F : ℚ → Bool | ¬ ∀ k : Fin 3, F ((k.val : ℚ) ^ 2 + p.1 * (k.val : ℚ) + p.2) = false}
    | Sum.inr p => {F : ℚ → Bool | ¬ ∀ k : Fin 17, F ((k.val : ℚ) ^ 2 + p.1 * (k.val : ℚ) + p.2) = true}
  have hTclosed : ∀ i : Index, IsClosed (T i) := by
    intro i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · dsimp [T]
      let x : Fin 3 → ℚ := fun k => (k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b
      have hset : {F : ℚ → Bool | ¬ ∀ k : Fin 3, F (x k) = false} =
          ⋃ k : Fin 3, {F : ℚ → Bool | F (x k) = true} := by
        ext F
        simp only [Set.mem_iUnion]
        constructor
        · intro hh
          by_contra hne
          apply hh
          intro k
          exact Bool.eq_false_of_not_eq_true (fun hk => hne ⟨k, hk⟩)
        · rintro ⟨k, hk⟩ hall
          simp [hall] at hk
      rw [hset]
      apply isClosed_iUnion_of_finite
      intro k
      exact IsClosed.preimage (continuous_apply (x k)) isClosed_singleton
    · dsimp [T]
      let x : Fin 17 → ℚ := fun k => (k.val : ℚ) ^ 2 + a * (k.val : ℚ) + b
      have hset : {F : ℚ → Bool | ¬ ∀ k : Fin 17, F (x k) = true} =
          ⋃ k : Fin 17, {F : ℚ → Bool | F (x k) = false} := by
        ext F
        simp only [Set.mem_iUnion]
        constructor
        · intro hh
          by_contra hne
          apply hh
          intro k
          exact Bool.eq_true_of_not_eq_false (fun hk => hne ⟨k, hk⟩)
        · rintro ⟨k, hk⟩ hall
          simp [hall] at hk
      rw [hset]
      apply isClosed_iUnion_of_finite
      intro k
      exact IsClosed.preimage (continuous_apply (x k)) isClosed_singleton
  have hFIP : ∀ s : Finset Index, (⋂ i ∈ s, T i).Nonempty := by
    intro s
    let d : Index → ℕ := fun i => (aa i).den * (bb i).den
    let q : ℕ := ∏ i ∈ s, d i
    have hqpos : 0 < q := by
      dsimp [q]
      apply Finset.prod_pos
      intro i hi
      exact Nat.mul_pos (aa i).den_pos (bb i).den_pos
    rcases h q hqpos with ⟨f, hf3, hf17⟩
    let F : ℚ → Bool := fun x => f ((q : ℚ) * x).num
    have hFdef : ∀ x : ℚ, F x = f ((q : ℚ) * x).num := fun x => rfl
    refine ⟨F, ?_⟩
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    have hdvd : d i ∣ q := by
      dsimp [q]
      exact Finset.dvd_prod_of_mem d hi
    have hda : (aa i).den ∣ q := dvd_trans (Nat.dvd_mul_right (aa i).den (bb i).den) hdvd
    have hdb : (bb i).den ∣ q := dvd_trans (Nat.dvd_mul_left (bb i).den (aa i).den) hdvd
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · dsimp [T]
      exact rational_quadratic_coloring_from_integer_scales_quadratic_coloring_constraint q f (n := 3) (target := false) hf3 (aa (Sum.inl (a, b))) (bb (Sum.inl (a, b))) hda hdb F hFdef
    · dsimp [T]
      exact rational_quadratic_coloring_from_integer_scales_quadratic_coloring_constraint q f (n := 17) (target := true) hf17 (aa (Sum.inr (a, b))) (bb (Sum.inr (a, b))) hda hdb F hFdef
  have hinter : (⋂ i : Index, T i).Nonempty :=
    CompactSpace.iInter_nonempty hTclosed hFIP
  rcases hinter with ⟨F, hF⟩
  have hFall : ∀ i : Index, F ∈ T i := by
    simpa only [Set.mem_iInter] using hF
  refine ⟨F, ?_, ?_⟩
  · intro a b
    have hh := hFall (Sum.inl (a, b))
    simpa [T] using hh
  · intro a b
    have hh := hFall (Sum.inr (a, b))
    simpa [T] using hh
