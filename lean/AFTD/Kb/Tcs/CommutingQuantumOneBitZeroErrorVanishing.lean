import AFTD.Prelude

/-!
# commuting_quantum_one_bit_zero_error_vanishing

Topic: communication   Node: a0bd406672b9

Provenance: helper lemma. step towards commuting_quantum_efficiency_one_bit

Let $\psi$ be a unit vector of a real Hilbert space on which Alice's effects $A^m_s$ and Bob's effects $B^{o}_{t,m}$ act as commuting projections with all Alice operators commuting with all Bob operators. If the total probability of the forbidden answer vanishes on every input pair — $\sum_m \langle\psi, A^m_s B^{\mathrm{false}}_{s,m}\psi\rangle = 0$ on equal inputs and $\sum_m \langle\psi, A^m_s B^{\mathrm{true}}_{t,m}\psi\rangle = 0$ on unequal inputs — then each term vanishes separately, i.e. $A^m_s B^{\mathrm{false}}_{s,m}\psi = 0$ for all $s,m$ and $A^m_s B^{\mathrm{true}}_{t,m}\psi = 0$ whenever $s \ne t$.
-/

/-- Zero error term by term: a forbidden conclusive answer kills the corresponding vector. -/
theorem commuting_quantum_one_bit_zero_error_vanishing
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {N : ℕ} (ψ : E)
    (A : Fin N → Fin 2 → E →L[ℝ] E) (B : Fin N → Fin 2 → Option Bool → E →L[ℝ] E)
    (hAproj : ∀ (s : Fin N) (m : Fin 2), IsStarProjection (A s m))
    (hBproj : ∀ (t : Fin N) (m : Fin 2) (o : Option Bool), IsStarProjection (B t m o))
    (hcomm : ∀ (s : Fin N) (m : Fin 2) (t : Fin N) (m' : Fin 2) (o : Option Bool),
      (A s m) * (B t m' o) = (B t m' o) * (A s m))
    (hz1 : ∀ s : Fin N, ∑ a : Fin 2, inner ℝ ψ (A s a (B s a (some false) ψ)) = 0)
    (hz2 : ∀ s t : Fin N, s ≠ t → ∑ a : Fin 2, inner ℝ ψ (A s a (B t a (some true) ψ)) = 0) :
    (∀ (s : Fin N) (a : Fin 2), A s a (B s a (some false) ψ) = 0) ∧
      ∀ (s t : Fin N) (a : Fin 2), s ≠ t → A s a (B t a (some true) ψ) = 0 := by
  -- For commuting star projections `P Q`, `⟪x, P (Q x)⟫ = ‖P (Q x)‖^2`.
  have key : ∀ (P Q : E →L[ℝ] E), IsStarProjection P → IsStarProjection Q → P * Q = Q * P →
      ∀ x : E, inner ℝ x (P (Q x)) = ‖P (Q x)‖ ^ 2 := by
    intro P Q hP hQ h x
    have hPQ : IsStarProjection (P * Q) := IsStarProjection.mul hP hQ h
    have main : inner ℝ x ((P * Q) x) = ‖(P * Q) x‖ ^ 2 := by
      have hadj : ContinuousLinearMap.adjoint (P * Q) = (P * Q) := by
        simpa using hPQ.isSelfAdjoint.adjoint_eq
      have hidem : (P * Q) ((P * Q) x) = (P * Q) x := by
        have h := hPQ.isIdempotentElem
        simpa using congrFun (congrArg DFunLike.coe h) x
      have h1 : inner ℝ ((P * Q) x) ((P * Q) x) = inner ℝ x ((P * Q) x) := by
        have := ContinuousLinearMap.adjoint_inner_left (P * Q) ((P * Q) x) x
        rw [hadj, hidem] at this
        exact this
      calc inner ℝ x ((P * Q) x) = inner ℝ ((P * Q) x) ((P * Q) x) := h1.symm
        _ = ‖(P * Q) x‖ ^ 2 := real_inner_self_eq_norm_sq ((P * Q) x)
    simpa using main
  -- A vanishing term of the sum forces the corresponding vector to vanish.
  have vanish : ∀ (P Q : E →L[ℝ] E), IsStarProjection P → IsStarProjection Q → P * Q = Q * P →
      inner ℝ ψ (P (Q ψ)) = 0 → P (Q ψ) = 0 := by
    intro P Q hP hQ h h0
    rw [key P Q hP hQ h ψ] at h0
    have : ‖P (Q ψ)‖ = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h0
    exact norm_eq_zero.mp this
  constructor
  · intro s a
    have hsum : ∑ b : Fin 2, inner ℝ ψ (A s b (B s b (some false) ψ)) = 0 := hz1 s
    have hnonneg : ∀ b ∈ Finset.univ, (0:ℝ) ≤ inner ℝ ψ (A s b (B s b (some false) ψ)) := by
      intro b _
      rw [key (A s b) (B s b (some false)) (hAproj s b) (hBproj s b (some false))
        (hcomm s b s b (some false))]
      positivity
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum a (Finset.mem_univ a)
    exact vanish (A s a) (B s a (some false)) (hAproj s a) (hBproj s a (some false))
      (hcomm s a s a (some false)) hterm
  · intro s t a hst
    have hsum : ∑ b : Fin 2, inner ℝ ψ (A s b (B t b (some true) ψ)) = 0 := hz2 s t hst
    have hnonneg : ∀ b ∈ Finset.univ, (0:ℝ) ≤ inner ℝ ψ (A s b (B t b (some true) ψ)) := by
      intro b _
      rw [key (A s b) (B t b (some true)) (hAproj s b) (hBproj t b (some true))
        (hcomm s b t b (some true))]
      positivity
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum a (Finset.mem_univ a)
    exact vanish (A s a) (B t a (some true)) (hAproj s a) (hBproj t a (some true))
      (hcomm s a t a (some true)) hterm
