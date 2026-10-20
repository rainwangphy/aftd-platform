import AFTD.Prelude
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# linear_code_supports_rate_of_transfer_matrix

Topic: information   Node: df4f8eae9ac1

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

Given M transmissions with endpoints snd, rcv on a capacitated network, a time horizon T > 0, a message dimension L > 0, capacity-respecting edge usage, encoding and decoding tables alpha, beta, gamma obeying causality and sender/receiver/decoder locality, and a transfer table W satisfying W m k j = alpha m k j + sum_{m'} beta m m' * W m' k j together with the decoding identity sum_m gamma k j m * W m k' j' = 1 if (k,j)=(k',j') and 0 otherwise, the resulting causal binary (or any-field) linear network code supports rate L/T.
-/

lemma linear_code_supports_rate_of_transfer_matrix_sum_comm_univ {ι κ R : Type} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (f : ι → κ → R) : (∑ i, ∑ k, f i k) = ∑ k, ∑ i, f i k := Finset.sum_comm

lemma linear_code_supports_rate_of_transfer_matrix_triple_sum_swap {ι κ μ R : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid R]
    (f : ι → κ → μ → R) : (∑ i, ∑ k, ∑ l, f i k l) = ∑ l, ∑ i, ∑ k, f i k l := by
  calc (∑ i, ∑ k, ∑ l, f i k l)
      = ∑ k, ∑ i, ∑ l, f i k l := linear_code_supports_rate_of_transfer_matrix_sum_comm_univ _
    _ = ∑ k, ∑ l, ∑ i, f i k l := by
          apply Finset.sum_congr rfl; intro k _
          exact linear_code_supports_rate_of_transfer_matrix_sum_comm_univ (fun i l => f i k l)
    _ = ∑ l, ∑ k, ∑ i, f i k l := linear_code_supports_rate_of_transfer_matrix_sum_comm_univ _
    _ = ∑ l, ∑ i, ∑ k, f i k l := by
          apply Finset.sum_congr rfl; intro l _
          exact linear_code_supports_rate_of_transfer_matrix_sum_comm_univ (fun k i => f i k l)

lemma linear_code_supports_rate_of_transfer_matrix_triple_sum_rot {ι κ μ R : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid R]
    (f : ι → κ → μ → R) : (∑ i, ∑ k, ∑ l, f i k l) = ∑ k, ∑ l, ∑ i, f i k l := by
  calc (∑ i, ∑ k, ∑ l, f i k l)
      = ∑ k, ∑ i, ∑ l, f i k l := linear_code_supports_rate_of_transfer_matrix_sum_comm_univ _
    _ = ∑ k, ∑ l, ∑ i, f i k l := by
          apply Finset.sum_congr rfl; intro k _
          exact linear_code_supports_rate_of_transfer_matrix_sum_comm_univ (fun i l => f i k l)

lemma linear_code_supports_rate_of_transfer_matrix_rec {F : Type} [Field F] {MM K L : Type} [Fintype MM] [Fintype K] [Fintype L]
    (a : MM → K → L → F) (b : MM → MM → F) (W : MM → K → L → F) (msg : K → L → F)
    (m : MM) (hW : ∀ (m : MM) (k : K) (j : L), W m k j = a m k j + ∑ m', b m m' * W m' k j) :
    (∑ k, ∑ j, W m k j * msg k j) = (∑ k, ∑ j, a m k j * msg k j) + ∑ m', b m m' * (∑ k, ∑ j, W m' k j * msg k j) := by
  calc (∑ k, ∑ j, W m k j * msg k j)
      = ∑ k, ∑ j, (a m k j + ∑ m', b m m' * W m' k j) * msg k j := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro j _
          rw [hW]
    _ = (∑ k, ∑ j, a m k j * msg k j) + ∑ k, ∑ j, (∑ m', b m m' * W m' k j) * msg k j := by
          simp only [add_mul, Finset.sum_add_distrib]
    _ = (∑ k, ∑ j, a m k j * msg k j) + ∑ k, ∑ j, ∑ m', (b m m' * W m' k j) * msg k j := by
          congr 1
          simp only [Finset.sum_mul]
    _ = (∑ k, ∑ j, a m k j * msg k j) + ∑ m', ∑ k, ∑ j, (b m m' * W m' k j) * msg k j := by
          congr 1
          exact linear_code_supports_rate_of_transfer_matrix_triple_sum_swap (fun k j m' => (b m m' * W m' k j) * msg k j)
    _ = (∑ k, ∑ j, a m k j * msg k j) + ∑ m', b m m' * (∑ k, ∑ j, W m' k j * msg k j) := by
          congr 1
          apply Finset.sum_congr rfl; intro m' _
          simp only [mul_assoc, Finset.mul_sum]

lemma linear_code_supports_rate_of_transfer_matrix_ite_collapse {F : Type} [Field F] {K L : Type} [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L] (msg : K → L → F) (k : K) (j : L) :
    (∑ k', ∑ j', (if k = k' ∧ j = j' then (1:F) else 0) * msg k' j') = msg k j := by
  rw [Finset.sum_eq_single (a := k)]
  · simp only [true_and, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (a := j)]
    · simp
    · intro j' _ hj'
      simp [Ne.symm hj']
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro k' _ hk'
    simp [Ne.symm hk']
  · intro h; exact absurd (Finset.mem_univ k) h

lemma linear_code_supports_rate_of_transfer_matrix_dec {F : Type} [Field F] {MM K L : Type} [Fintype MM] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (W : MM → K → L → F) (γ : K → L → MM → F) (msg : K → L → F) (k : K) (j : L)
    (hD : ∀ (k : K) (j : L) (k' : K) (j' : L), (∑ m, γ k j m * W m k' j') = if k = k' ∧ j = j' then 1 else 0) :
    msg k j = ∑ m, γ k j m * (∑ k', ∑ j', W m k' j' * msg k' j') := by
  symm
  calc (∑ m, γ k j m * (∑ k', ∑ j', W m k' j' * msg k' j'))
      = ∑ m, ∑ k', ∑ j', γ k j m * (W m k' j' * msg k' j') := by
          simp only [Finset.mul_sum]
    _ = ∑ k', ∑ j', ∑ m, γ k j m * (W m k' j' * msg k' j') := linear_code_supports_rate_of_transfer_matrix_triple_sum_rot _
    _ = ∑ k', ∑ j', (∑ m, γ k j m * W m k' j') * msg k' j' := by
          apply Finset.sum_congr rfl; intro k' _
          apply Finset.sum_congr rfl; intro j' _
          simp only [← mul_assoc, Finset.sum_mul]
    _ = ∑ k', ∑ j', (if k = k' ∧ j = j' then (1:F) else 0) * msg k' j' := by
          apply Finset.sum_congr rfl; intro k' _
          apply Finset.sum_congr rfl; intro j' _
          rw [hD k j k' j']
    _ = msg k j := linear_code_supports_rate_of_transfer_matrix_ite_collapse msg k j

/-- A finite transfer-matrix certificate turns the code half of a witness into decidable table equations. -/
theorem linear_code_supports_rate_of_transfer_matrix
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    {M T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (snd rcv : Fin M → V) (hne : ∀ m, snd m ≠ rcv m)
    (hcap : ∀ e : Sym2 V,
      ((Finset.univ.filter (fun m : Fin M => s(snd m, rcv m) = e)).card : ℝ) ≤ (T : ℝ) * net.cap e)
    (α : Fin M → K → Fin L → F) (β : Fin M → Fin M → F) (γ : K → Fin L → Fin M → F)
    (W : Fin M → K → Fin L → F)
    (hcausal : ∀ m m', β m m' ≠ 0 → m' < m)
    (hsnd : ∀ (m : Fin M) (k : K) (j : Fin L), α m k j ≠ 0 → sess.src k = snd m)
    (hrcv : ∀ (m m' : Fin M), β m m' ≠ 0 → rcv m' = snd m)
    (hdec : ∀ (k : K) (j : Fin L) (m : Fin M), γ k j m ≠ 0 → rcv m = sess.tgt k)
    (hW : ∀ (m : Fin M) (k : K) (j : Fin L), W m k j = α m k j + ∑ m', β m m' * W m' k j)
    (hD : ∀ (k : K) (j : Fin L) (k' : K) (j' : Fin L),
      (∑ m, γ k j m * W m k' j') = if k = k' ∧ j = j' then 1 else 0) :
    LinearCodeSupportsRate F net sess ((L : ℝ) / (T : ℝ)) := by
  refine ⟨{ M := M, T := T, L := L, hT := hT, hL := hL, snd := snd, rcv := rcv,
            snd_ne_rcv := hne, cap_le := hcap, α := α, β := β, γ := γ,
            causal := hcausal, snd_local := hsnd, rcv_local := hrcv, dec_local := hdec,
            correct := ?_ }, le_refl _⟩
  intro msg
  exact ⟨fun m => ∑ k, ∑ j, W m k j * msg k j,
          fun m => linear_code_supports_rate_of_transfer_matrix_rec α β W msg m hW,
          fun k j => linear_code_supports_rate_of_transfer_matrix_dec W γ msg k j hD⟩
