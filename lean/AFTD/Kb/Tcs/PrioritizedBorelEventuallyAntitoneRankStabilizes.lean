import AFTD.Prelude

/-!
# prioritized_borel_eventually_antitone_rank_stabilizes

Topic: automata   Node: ab180e8fb75b

Provenance: helper lemma.

An eventually nonincreasing sequence of natural-number ranks eventually stabilizes.
-/

theorem prioritized_borel_eventually_antitone_rank_stabilizes (r : ℕ → ℕ) (N : ℕ)
    (hstep : ∀ n ≥ N, r (n+1) ≤ r n) :
    ∃ K ≥ N, ∀ n ≥ K, r n = r K := by
  let f : ℕ → ℕ := fun n => r (N+n)
  have hmono : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    have h := hstep (N+n) (by omega)
    simpa [f, Nat.add_assoc] using h
  obtain ⟨K, hK⟩ := WellFoundedLT.antitone_chain_condition hmono
  refine ⟨N+K, by omega, ?_⟩
  intro n hn
  have hstart : N ≤ n := by omega
  have hi : K ≤ n-N := by omega
  have h := hK (n-N) hi
  change r (N+K) = r (N+(n-N)) at h
  simpa [Nat.add_sub_of_le hstart] using h.symm
