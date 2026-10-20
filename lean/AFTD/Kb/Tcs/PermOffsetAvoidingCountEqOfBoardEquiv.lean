import AFTD.Prelude
import AFTD.Kb.Tcs.PermOffsetAvoidingCount

/-!
# perm_offset_avoiding_count_eq_of_board_equiv

Topic: combinatorics   Node: 55e0218003dc

Provenance: helper lemma. lemma for arXiv:2610.23958 Proposition 6.2 (PR-301): counts of avoiding permutations are invariant under relabelling rows and columns of the board

If bijections sigma (of rows) and rho (of columns) of Fin n carry the forbidden squares of the offset set S exactly onto those of S' -- n divides j - i - s for some s in S iff n divides rho(j) - sigma(i) - s' for some s' in S' -- then a_S(n) = a_{S'}(n): pi -> rho o pi o sigma^-1 is a bijection between the avoiding permutations.
-/

theorem perm_offset_avoiding_count_eq_of_board_equiv (n : ℕ) (S S' : Finset ℤ)
    (σ ρ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, (∃ s ∈ S, (n : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) - s) ↔
      (∃ s ∈ S', (n : ℤ) ∣ ((ρ j : ℕ) : ℤ) - ((σ i : ℕ) : ℤ) - s)) :
    perm_offset_avoiding_count n S = perm_offset_avoiding_count n S' := by
  unfold perm_offset_avoiding_count
  refine Finset.card_bij (fun π _ => σ.symm.trans (π.trans ρ)) ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro i s hs hdvd
    obtain ⟨s', hs', hd'⟩ := (h (σ.symm i) (π (σ.symm i))).2 ⟨s, hs, by simpa using hdvd⟩
    exact hπ _ s' hs' hd'
  · intro a _ b _ hab
    refine Equiv.ext fun x => ?_
    have := congrArg (fun e : Equiv.Perm (Fin n) => e (σ x)) hab
    simpa using this
  · intro π' hπ'
    refine ⟨σ.trans (π'.trans ρ.symm), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ' ⊢
      intro i s hs hdvd
      obtain ⟨s', hs', hd'⟩ := (h i ((σ.trans (π'.trans ρ.symm)) i)).1 ⟨s, hs, hdvd⟩
      apply hπ' (σ i) s' hs'
      simpa using hd'
    · ext x; simp
