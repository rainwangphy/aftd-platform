import AFTD.Prelude
import AFTD.Kb.Tcs.LinearCodeSupportsRateOfTransferMatrix
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# causal_linear_network_code_of_transfer_matrix

Topic: information   Node: 8f378dd555f0

Provenance: helper lemma. step towards single_slot_binary_linear_coding_advantage

The construction half of the transfer-matrix criterion, returned as the code itself: explicit transmission endpoints, horizon T, message dimension L and encoding/decoding tables over any field that respect the capacities and locality, together with a transfer table W solving the local encoding equations and inverting the decoding identity, are the data of an actual deterministic causal linear network code with $\mathtt{code}.T = T$ and $\mathtt{code}.L = L$.
-/

/-- Table-level data satisfying the transfer-matrix hypotheses determine an actual causal linear code with the same T and L. -/
theorem causal_linear_network_code_of_transfer_matrix
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
    ∃ code : CausalLinearNetworkCode V K F net sess, code.T = T ∧ code.L = L := by
  refine ⟨{ M := M, T := T, L := L, hT := hT, hL := hL,
            snd := snd, rcv := rcv, snd_ne_rcv := hne, cap_le := hcap,
            α := α, β := β, γ := γ,
            causal := hcausal, snd_local := hsnd, rcv_local := hrcv, dec_local := hdec,
            correct := ?_ }, rfl, rfl⟩
  intro msg
  refine ⟨fun m => ∑ k, ∑ j, W m k j * msg k j, ?_, ?_⟩
  · intro m
    exact linear_code_supports_rate_of_transfer_matrix_rec α β W msg m hW
  · intro k j
    exact linear_code_supports_rate_of_transfer_matrix_dec W γ msg k j hD
