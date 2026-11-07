import AFTD.Prelude

/-!
# equality_classical_behaviour

Topic: communication   Node: 2cb6c53560d3

Provenance: helper lemma. step towards commuting_quantum_efficiency_classical_lower_bound

The behaviour of the shared-random-subset equality protocol: on shared randomness r ∈ ZMod N, Alice sends the clipped message (s + r) mod N with K − 1 concrete values and a 'fail' message K − 1; on a concrete message m Bob outputs 'true' if (t + r) mod N = m and 'false' otherwise, and abstains on the fail message. The probability p(s,(t,a),a,o) is the fraction of r realizing message a and output o.
-/

/-- The classical shared-randomness behaviour for equality certification: Alice clips (s + r) to a concrete message value in Fin (K−1) with fallback message K−1, Bob answers conclusively on concrete messages by comparing (t + r) with the received message; probability = fraction of randomness r realizing (message, output). -/
noncomputable def equality_classical_behaviour (N K : ℕ) [NeZero N] (hK : 1 ≤ K) :
    Fin N → Fin N × Fin K → Fin K → Option Bool → ℝ := fun (s : Fin N) (q : Fin N × Fin K) (x : Fin K) (o : Option Bool) =>
  ((Finset.univ.filter (fun r : ZMod N =>
      (if h : ((s.val : ZMod N) + r).val < K - 1 then
          (⟨((s.val : ZMod N) + r).val, h.trans_le (Nat.sub_le K 1)⟩ : Fin K)
        else ⟨K - 1, by omega⟩) = x ∧
      (if x.val < K - 1 then
          (if r + (q.1.val : ZMod N) = (x.val : ZMod N) then some true else some false)
        else none) = o)).card : ℝ) / (N : ℝ)
