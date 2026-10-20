import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# CausalLinearNetworkCode

Topic: information   Node: 0b4cc9c02d82

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

A structure CausalLinearNetworkCode parameterized by a finite vertex type V with decidable equality, a finite session type K with decidable equality, a field F, a capacitated network net on V, and unicast sessions sess on V indexed by K. It packages: positive integers T (time horizon) and L (message dimension) with 0 < T and 0 < L; total transmissions M : ℕ; sender and receiver maps snd, rcv : Fin M → V with snd m ≠ rcv m for all m; edge capacity condition that for every e : Sym2 V, the number of transmissions m along e is at most (T : ℝ) * net.cap e; encoding matrices α : Fin M → K → Fin L → F and β : Fin M → Fin M → F; decoding matrix γ : K → Fin L → Fin M → F; index-based causality stating that β m m' ≠ 0 implies m' < m; sender locality stating α m k j ≠ 0 implies sess.src k = snd m; receiver locality stating β m m' ≠ 0 implies rcv m' = snd m; decoding locality stating γ k j m ≠ 0 implies rcv m = sess.tgt k; and correctness asserting that for every message msg : K → Fin L → F there exists a transmission valuation val : Fin M → F satisfying the local encoding equations val m = (∑ k, ∑ j, α m k j * msg k j) + (∑ m', β m m' * val m') for all m, and decoding equations msg k j = ∑ m, γ k j m * val m for all k and j.
-/

/-- A deterministic causal linear network code over a field F on a capacitated network. -/
structure CausalLinearNetworkCode (V : Type) [Fintype V] [DecidableEq V] (K : Type) [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K) where
  M : ℕ
  T : ℕ
  L : ℕ
  hT : 0 < T
  hL : 0 < L
  snd : Fin M → V
  rcv : Fin M → V
  snd_ne_rcv : ∀ m, snd m ≠ rcv m
  cap_le : ∀ e : Sym2 V,
    ((Finset.univ.filter (fun m => s(snd m, rcv m) = e)).card : ℝ) ≤ (T : ℝ) * net.cap e
  α : Fin M → K → Fin L → F
  β : Fin M → Fin M → F
  γ : K → Fin L → Fin M → F
  causal : ∀ m m', β m m' ≠ 0 → m' < m
  snd_local : ∀ m k j, α m k j ≠ 0 → sess.src k = snd m
  rcv_local : ∀ m m', β m m' ≠ 0 → rcv m' = snd m
  dec_local : ∀ k j m, γ k j m ≠ 0 → rcv m = sess.tgt k
  correct : ∀ msg : K → Fin L → F,
    ∃ val : Fin M → F,
      (∀ m, val m = (∑ k, ∑ j, α m k j * msg k j) + (∑ m', β m m' * val m')) ∧
      (∀ k j, msg k j = ∑ m, γ k j m * val m)
