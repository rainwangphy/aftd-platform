import AFTD.Prelude

/-!
# higher_bruhat_exists_modular_level_set_card_ge

Topic: combinatorics   Node: d5b5c1a52ba7

Provenance: helper lemma. arXiv:2611.17465, Section 2.1, Proof of Proposition 2

For all natural numbers n and k with 0 < n and 0 < k, there exists a natural number c < n such that the ceiling of choose(n, k+1) / n (in ℝ) is at most the cardinality of the family of subsets A of Fin n of size k+1 satisfying (∑ a ∈ A, a.val) % n = c.
-/

private lemma higher_bruhat_exists_modular_level_set_card_ge_fiber (n : ℕ) (hn : 0 < n) {α : Type*}
    (S : Finset α) (g : α → ℕ) (hg : ∀ A ∈ S, g A < n) :
    ∃ c < n, Nat.ceil ((S.card : ℝ) / (n : ℝ)) ≤ (S.filter (fun A => g A = c)).card := by
  classical
  obtain ⟨c₀, hc₀, hmax⟩ := Finset.exists_max_image (Finset.range n)
    (fun c => (S.filter (fun A => g A = c)).card) ⟨0, Finset.mem_range.mpr hn⟩
  refine ⟨c₀, Finset.mem_range.mp hc₀, ?_⟩
  have hmaps : Set.MapsTo g (↑S) (↑(Finset.range n)) := by
    intro a ha
    simp only [Finset.coe_range, Set.mem_Iio]
    exact hg a ha
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∑ c ∈ Finset.range n, (S.filter (fun A => g A = c)).card
      ≤ n * (S.filter (fun A => g A = c₀)).card := by
    calc ∑ c ∈ Finset.range n, (S.filter (fun A => g A = c)).card
        ≤ ∑ _c ∈ Finset.range n, (S.filter (fun A => g A = c₀)).card :=
          Finset.sum_le_sum (fun c hc => hmax c hc)
      _ = n * (S.filter (fun A => g A = c₀)).card := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hkey : S.card ≤ n * (S.filter (fun A => g A = c₀)).card := hsum.trans_le hle
  rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hn)]
  have h' : (S.card : ℝ) ≤ (n : ℝ) * ((S.filter (fun A => g A = c₀)).card : ℝ) := by
    exact_mod_cast hkey
  linarith

/-- By the pigeonhole principle, some modular level set has cardinality at least ceil(choose(n, k+1) / n). -/
lemma higher_bruhat_exists_modular_level_set_card_ge (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∃ c < n, Nat.ceil ((n.choose (k + 1) : ℝ) / (n : ℝ)) ≤
      ((Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1)).filter
        (fun A => (∑ a ∈ A, a.val) % n = c)).card := by
  classical
  have hScard : (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1)).card
      = n.choose (k + 1) := by
    have heq : Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1)
        = (Finset.univ : Finset (Fin n)).powersetCard (k + 1) := by
      ext A
      simp [Finset.mem_powersetCard]
    rw [heq, Finset.card_powersetCard]
    simp
  obtain ⟨c, hc, h⟩ := higher_bruhat_exists_modular_level_set_card_ge_fiber n hn
    (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k + 1))
    (fun A => (∑ a ∈ A, a.val) % n)
    (fun A _ => Nat.mod_lt _ hn)
  rw [hScard] at h
  exact ⟨c, hc, h⟩
