import AFTD.Prelude

/-!
# condorcet_six_balanced_top_structure

Topic: social_choice   Node: 7967c558398a

Provenance: helper lemma. step towards condorcet_dimension_le_three

With six candidates, if every three-candidate set contains the top choice of at most half of the voters, then the top-choice profile is completely rigid: every candidate is the top choice of exactly n/6 voters.
-/

/-- In the balanced regime with six candidates every candidate has exactly n/6 top-choice voters. -/
theorem condorcet_six_balanced_top_structure (n : ℕ) (P : Fin n → Equiv.Perm (Fin 6))
    (hbal : ∀ S : Finset (Fin 6), S.card = 3 →
      2 * (Finset.univ.filter fun v => (P v).symm ⟨0, by norm_num⟩ ∈ S).card ≤ n) :
    ∀ c : Fin 6, 6 * (Finset.univ.filter fun v => (P v).symm ⟨0, by norm_num⟩ = c).card = n := by
  classical
  let top : Fin n → Fin 6 := fun v => (P v).symm ⟨0, by norm_num⟩
  let fib : Fin 6 → Finset (Fin n) := fun c => Finset.univ.filter fun v => top v = c
  let t : Fin 6 → ℕ := fun c => (fib c).card
  have hbal' : ∀ S : Finset (Fin 6), S.card = 3 →
      2 * (Finset.univ.filter fun v => top v ∈ S).card ≤ n := hbal
  have hsum : ∑ c : Fin 6, t c = n := by
    have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := top)
      (by intro a _; simp)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [← h]
  have htop_card : ∀ S : Finset (Fin 6), (Finset.univ.filter fun v => top v ∈ S).card = ∑ c ∈ S, t c := by
    intro S
    have hdisj : (↑S : Set (Fin 6)).PairwiseDisjoint fib := by
      intro c _ d _ hcd
      rw [Function.onFun, Finset.disjoint_left]
      intro v hv hv'
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
      exact hcd (hv.symm.trans hv')
    have hbij : S.biUnion fib = Finset.univ.filter fun v => top v ∈ S := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, fib]
      constructor
      · rintro ⟨c, hcS, htc⟩; rw [htc]; exact hcS
      · intro hv; exact ⟨top v, hv, rfl⟩
    rw [← hbij, Finset.card_biUnion hdisj]
  have hS_eq : ∀ S : Finset (Fin 6), S.card = 3 → 2 * ∑ c ∈ S, t c = n := by
    intro S hS
    have hle1 : 2 * ∑ c ∈ S, t c ≤ n := by rw [← htop_card S]; exact hbal' S hS
    have hcomp : Sᶜ.card = 3 := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hle2 : 2 * ∑ c ∈ Sᶜ, t c ≤ n := by rw [← htop_card Sᶜ]; exact hbal' Sᶜ hcomp
    have hsplit : ∑ c ∈ S, t c + ∑ c ∈ Sᶜ, t c = n := by
      rw [Finset.sum_add_sum_compl, hsum]
    omega
  have htriple : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      2 * (t a + t b + t c) = n := by
    intro a b c hab hac hbc
    have hScard : ({a, b, c} : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hbc]
      · simp [hab, hac]
    have h := hS_eq {a, b, c} hScard
    have hsum3 : ∑ x ∈ ({a, b, c} : Finset (Fin 6)), t x = t a + t b + t c := by
      rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
          Finset.sum_singleton]
      omega
    rwa [hsum3] at h
  have h32 : t 3 = t 2 := by
    have h1 := htriple 0 1 2 (by decide) (by decide) (by decide)
    have h2 := htriple 0 1 3 (by decide) (by decide) (by decide)
    omega
  have h03 : t 0 = t 3 := by
    have h1 := htriple 0 1 2 (by decide) (by decide) (by decide)
    have h2 := htriple 1 2 3 (by decide) (by decide) (by decide)
    omega
  have h13 : t 1 = t 3 := by
    have h1 := htriple 0 1 2 (by decide) (by decide) (by decide)
    have h2 := htriple 0 2 3 (by decide) (by decide) (by decide)
    omega
  have h42 : t 4 = t 2 := by
    have h1 := htriple 0 1 2 (by decide) (by decide) (by decide)
    have h2 := htriple 0 1 4 (by decide) (by decide) (by decide)
    omega
  have h52 : t 5 = t 2 := by
    have h1 := htriple 0 1 2 (by decide) (by decide) (by decide)
    have h2 := htriple 0 1 5 (by decide) (by decide) (by decide)
    omega
  have hconst : ∀ c : Fin 6, t c = t 2 := by
    intro c
    fin_cases c
    · show t 0 = t 2; rw [h03, h32]
    · show t 1 = t 2; exact h13.trans h32
    · rfl
    · show t 3 = t 2; exact h32
    · show t 4 = t 2; exact h42
    · show t 5 = t 2; exact h52
  have h6 : ∑ c : Fin 6, t c = 6 * t 2 := by
    rw [show ∑ c : Fin 6, t c = ∑ c : Fin 6, t 2 from Finset.sum_congr rfl fun c _ => hconst c]
    simp [Finset.sum_const, Fintype.card_fin]
  intro c
  show 6 * t c = n
  rw [hconst c, ← h6]
  exact hsum
