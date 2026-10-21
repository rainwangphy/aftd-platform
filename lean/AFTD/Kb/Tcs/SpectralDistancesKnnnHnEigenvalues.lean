import AFTD.Prelude
import AFTD.Kb.Tcs.KnnnEigenvalues
import AFTD.Kb.Tcs.HnEigenvalues
import AFTD.Kb.Tcs.HnEigenvalueShiftIdentity
import AFTD.Kb.Tcs.SpectralDistanceL1
import AFTD.Kb.Tcs.SpectralDistanceL2Sq

/-!
# spectral_distances_knnn_hn_eigenvalues

Topic: graphs   Node: ce98723547ef

Provenance: formalization of a published result. Source: arXiv:2610.18636 Theorem 5

Let n >= 2 and let l1, l2, l3 be real numbers such that l1 + l2 + l3 = n, l1 < 2 * n, 0 < l2, and -n < l3. Let Lam = 2 * n - l1. Then 0 < Lam, the Manhattan spectral distance spectral_distance_l1 between knnn_eigenvalues n and hn_eigenvalues n l1 l2 l3 equals 2 * Lam, and the squared Euclidean spectral distance spectral_distance_l2_sq equals 2 * (Lam ^ 2 - Lam * l2 + l2 ^ 2).
-/

open Finset

theorem spectral_distances_knnn_hn_eigenvalues_helper {m : ℕ} (f : Fin m → ℝ) (a b c : Fin m)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h_zero : ∀ x : Fin m, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    ∑ x, f x = f a + f b + f c := by
  have hsub : ({a, b, c} : Finset (Fin m)) ⊆ univ := subset_univ _
  have h_eq : ∑ x, f x = ∑ x ∈ ({a, b, c} : Finset (Fin m)), f x := by
    apply (sum_subset hsub _).symm
    intro x _ hx
    simp only [mem_insert, mem_singleton, not_or] at hx
    exact h_zero x hx.1 hx.2.1 hx.2.2
  rw [h_eq]
  have hbc' : b ∉ ({c} : Finset (Fin m)) := by simp [hbc]
  have ha' : a ∉ ({b, c} : Finset (Fin m)) := by simp [hab, hac]
  rw [sum_insert ha', sum_insert hbc', sum_singleton, add_assoc]

/-- Closed form Manhattan and squared Euclidean spectral distances between knnn_eigenvalues and hn_eigenvalues. -/
theorem spectral_distances_knnn_hn_eigenvalues (n : ℕ) (hle : 2 ≤ n)
    (l1 l2 l3 : ℝ)
    (hsum : l1 + l2 + l3 = (n : ℝ))
    (hl1 : l1 < 2 * (n : ℝ))
    (hl2 : 0 < l2)
    (hl3 : -(n : ℝ) < l3) :
    let Lam := 2 * (n : ℝ) - l1
    0 < Lam ∧
    spectral_distance_l1 (knnn_eigenvalues n) (hn_eigenvalues n l1 l2 l3) = 2 * Lam ∧
    spectral_distance_l2_sq (knnn_eigenvalues n) (hn_eigenvalues n l1 l2 l3) =
      2 * (Lam ^ 2 - Lam * l2 + l2 ^ 2) := by
  intro Lam
  have hLam : 0 < Lam := sub_pos.mpr hl1
  have hshift : (n : ℝ) + l3 = Lam - l2 := hn_eigenvalue_shift_identity n l1 l2 l3 hsum
  have hpos3 : 0 < Lam - l2 := by
    rw [← hshift]
    linarith [hl3]
  let i0 : Fin (3 * n) := ⟨0, by omega⟩
  let i1 : Fin (3 * n) := ⟨1, by omega⟩
  let i2 : Fin (3 * n) := ⟨3 * n - 2, by omega⟩
  have hab : i0 ≠ i1 := by intro h; injection h; omega
  have hbc : i1 ≠ i2 := by intro h; injection h; omega
  have hac : i0 ≠ i2 := by intro h; injection h; omega

  have heval0 : knnn_eigenvalues n i0 - hn_eigenvalues n l1 l2 l3 i0 = Lam := by
    rfl
  have heval1 : knnn_eigenvalues n i1 - hn_eigenvalues n l1 l2 l3 i1 = -l2 := by
    dsimp [i1, knnn_eigenvalues, hn_eigenvalues]
    have hlt : 1 < 3 * n - 2 := by omega
    simp [hlt]
  have heval2 : knnn_eigenvalues n i2 - hn_eigenvalues n l1 l2 l3 i2 = -(Lam - l2) := by
    dsimp [i2, knnn_eigenvalues, hn_eigenvalues]
    have h0 : 3 * n - 2 ≠ 0 := by omega
    have h1 : 3 * n - 2 ≠ 1 := by omega
    have hlt : ¬ (3 * n - 2 < 3 * n - 2) := by omega
    simp only [h0, h1, hlt, ↓reduceIte]
    linarith [hshift]
  have heval_other : ∀ x : Fin (3 * n), x ≠ i0 → x ≠ i1 → x ≠ i2 →
      knnn_eigenvalues n x - hn_eigenvalues n l1 l2 l3 x = 0 := by
    intro x h0 h1 h2
    have hx0 : (x : ℕ) ≠ 0 := by intro h; apply h0; ext; exact h
    have hx1 : (x : ℕ) ≠ 1 := by intro h; apply h1; ext; exact h
    have hx2 : (x : ℕ) ≠ 3 * n - 2 := by intro h; apply h2; ext; exact h
    dsimp [knnn_eigenvalues, hn_eigenvalues]
    simp only [hx0, hx1, hx2, ↓reduceIte]
    split_ifs <;> ring

  refine ⟨hLam, ?_, ?_⟩
  · -- spectral_distance_l1
    dsimp [spectral_distance_l1]
    rw [spectral_distances_knnn_hn_eigenvalues_helper
        (fun i => |knnn_eigenvalues n i - hn_eigenvalues n l1 l2 l3 i|)
        i0 i1 i2 hab hbc hac]
    · rw [heval0, heval1, heval2]
      rw [abs_of_pos hLam]
      rw [abs_neg, abs_of_pos hl2]
      rw [abs_neg, abs_of_pos hpos3]
      ring
    · intro x h0 h1 h2
      rw [heval_other x h0 h1 h2]
      simp
  · -- spectral_distance_l2_sq
    dsimp [spectral_distance_l2_sq]
    rw [spectral_distances_knnn_hn_eigenvalues_helper
        (fun i => (knnn_eigenvalues n i - hn_eigenvalues n l1 l2 l3 i) ^ 2)
        i0 i1 i2 hab hbc hac]
    · rw [heval0, heval1, heval2]
      ring
    · intro x h0 h1 h2
      rw [heval_other x h0 h1 h2]
      simp
