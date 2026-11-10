import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber
import AFTD.Kb.Tcs.NumericalSemigroupMultiplicity
import AFTD.Kb.Tcs.NumericalSemigroupGenus

/-!
# numerical_semigroup_exists_at_m_eq_succ_frobenius

Topic: combinatorics   Node: e115595c82e6

Provenance: helper lemma. arXiv:2611.11559, Lemma 2.3

For every positive integer F, there exists a numerical semigroup S with Frobenius number F, multiplicity F + 1, and genus F.
-/

/-- Existence of the unique numerical semigroup with multiplicity F + 1 and Frobenius number F. -/
theorem numerical_semigroup_exists_at_m_eq_succ_frobenius (F : ℕ) (hF : 0 < F) :
    ∃ S : NumericalSemigroup,
      numerical_semigroup_frobenius_number S = F ∧
      numerical_semigroup_multiplicity S = F + 1 ∧
      numerical_semigroup_genus S = F := by
  open Set in
  let M : AddSubmonoid ℕ :=
    { carrier := {n : ℕ | n = 0 ∨ F + 1 ≤ n}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        rcases ha with rfl | ha
        · simpa using hb
        · rcases hb with rfl | hb
          · right
            simpa using ha
          · right
            omega }
  have hfin : (M : Set ℕ)ᶜ.Finite := by
    apply Set.Finite.subset (Set.finite_lt_nat (F + 1))
    intro n hn
    have hn' : ¬ (n = 0 ∨ F + 1 ≤ n) := by simpa [M] using hn
    have h2 : ¬ F + 1 ≤ n := (not_or.mp hn').2
    simpa using not_le.mp h2
  let S : NumericalSemigroup := ⟨M, hfin⟩
  have hcompl : (S.toAddSubmonoid : Set ℕ)ᶜ = Set.Icc 1 F := by
    ext n
    change n ∉ (M : Set ℕ) ↔ n ∈ Set.Icc 1 F
    simp only [M, Set.mem_Icc]
    constructor
    · intro hn
      have h := not_or.mp hn
      constructor <;> omega
    · rintro ⟨h1, h2⟩ hmem
      have hmem' : n = 0 ∨ F + 1 ≤ n := by simpa [M] using hmem
      omega
  have hpos : {x : ℕ | x ∈ (S.toAddSubmonoid : Set ℕ) ∧ 0 < x} = Set.Ici (F + 1) := by
    ext n
    change (n ∈ (M : Set ℕ) ∧ 0 < n) ↔ n ∈ Set.Ici (F + 1)
    simp only [M, Set.mem_Ici]
    constructor
    · rintro ⟨h, hnpos⟩
      rcases h with h0 | hge
      · omega
      · exact hge
    · intro hge
      exact ⟨Or.inr hge, by omega⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · change sSup ((S.toAddSubmonoid : Set ℕ)ᶜ) = F
    rw [hcompl]
    exact csSup_Icc hF
  · change sInf {x : ℕ | x ∈ (S.toAddSubmonoid : Set ℕ) ∧ 0 < x} = F + 1
    rw [hpos]
    exact csInf_Ici
  · change ((S.toAddSubmonoid : Set ℕ)ᶜ).ncard = F
    rw [hcompl, Set.ncard_Icc_nat]
    omega
