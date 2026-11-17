import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedFactorizationEquivSigma

/-!
# orderedFactorization_finite

Topic: combinatorics   Node: c5e28444f0c8

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): helper for H(m) (Section 3)

Every natural number has finitely many ordered factorizations into integers greater than 1.
-/

theorem orderedFactorization_finite (n : ℕ) :
    Finite {l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = n} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hpos : ∀ l : List ℕ, (∀ a ∈ l, 1 < a) → 0 < l.prod := fun l hl =>
      List.prod_pos (fun a ha => by have := hl a ha; omega)
    rcases (by omega : n = 0 ∨ n = 1 ∨ 1 < n) with rfl | rfl | hn
    · have : IsEmpty {l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = 0} :=
        ⟨fun l => (hpos l.1 l.2.1).ne' l.2.2⟩
      infer_instance
    · have : Subsingleton {l : List ℕ // (∀ a ∈ l, 1 < a) ∧ l.prod = 1} := by
        constructor
        have hnil : ∀ l : List ℕ, (∀ a ∈ l, 1 < a) → l.prod = 1 → l = [] := by
          intro l h1 h2
          cases l with
          | nil => rfl
          | cons a t =>
            have ha := h1 a (by simp)
            simp only [List.prod_cons] at h2
            have := Nat.eq_one_of_mul_eq_one_right h2
            omega
        rintro ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩
        exact Subtype.ext ((hnil x hx1 hx2).trans (hnil y hy1 hy2).symm)
      infer_instance
    · have : ∀ d : n.properDivisors,
          Finite {t : List ℕ // (∀ a ∈ t, 1 < a) ∧ t.prod = d.1} :=
        fun d => ih d.1 (Nat.mem_properDivisors.mp d.2).2
      obtain ⟨e⟩ := orderedFactorization_equiv_sigma n hn
      exact Finite.of_equiv _ e.symm
