import AFTD.Prelude

/-!
# commuting_quantum_lueders_prefix

Topic: communication   Node: e5ea8a989211

Provenance: helper lemma. step towards commuting_quantum_efficiency_one_bit

For Alice's one-message effects A_t indexed by the labels t ∈ Fin N, the k-th Lüders prefix is the product W_k = ∏_{j<k} (1 − A_j) of the 'no outcome yet' operators of the N sequential tests, in the label order of Fin N (and W_k = W_{N-1} for k ≥ N, so the definition is total).
-/

/-- The 'no outcome yet' operator of the sequential (Lüders) measurement testing the effects A_0, A_1, ... in the order of `Fin N`. -/
noncomputable def commuting_quantum_lueders_prefix {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (A : Fin N → E →L[ℝ] E) : ℕ → E →L[ℝ] E := fun n =>
  Nat.rec (motive := fun _ => E →L[ℝ] E) 1
    (fun k ih => if h : k < N then ih * (1 - A ⟨k, h⟩) else ih) n
