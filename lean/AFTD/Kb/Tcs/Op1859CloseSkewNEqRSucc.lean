import AFTD.Prelude
import AFTD.Kb.Tcs.HammingCloseSkewSystem

/-!
# op_1859_close_skew_n_eq_r_succ

Topic: combinatorics   Node: b223d4a81490

Provenance: formalization of a published result. Source: arXiv:2611.20820 Sec. 5.7

Let r >= 1 be a natural number. If v and w are sequences of k points in {0,1}^(r+1) forming a close-skew system of radius r, then k <= 2^r.
-/

def op_1859_close_skew_n_eq_r_succ_notVec {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun a => !x a

theorem op_1859_close_skew_n_eq_r_succ_notVec_injective {n : ℕ} :
    Function.Injective (op_1859_close_skew_n_eq_r_succ_notVec (n := n)) := by
  intro x y h
  ext i
  have := congr_fun h i
  dsimp [op_1859_close_skew_n_eq_r_succ_notVec] at this
  simpa using this

theorem op_1859_close_skew_n_eq_r_succ_hammingDist_notVec {n : ℕ} (x : Fin n → Bool) :
    hammingDist x (op_1859_close_skew_n_eq_r_succ_notVec x) = n := by
  change (Finset.filter (fun i => x i ≠ op_1859_close_skew_n_eq_r_succ_notVec x i) Finset.univ).card = n
  have h_univ : (Finset.filter (fun i => x i ≠ op_1859_close_skew_n_eq_r_succ_notVec x i) Finset.univ) = Finset.univ := by
    ext i
    simp [op_1859_close_skew_n_eq_r_succ_notVec]
  rw [h_univ, Finset.card_univ, Fintype.card_fin]

/-- The close-skew set-pair bound holds in the codimension-one case n = r + 1. -/
theorem op_1859_close_skew_n_eq_r_succ {r k : ℕ} (hr : 1 ≤ r)
    (v w : Fin k → Fin (r + 1) → Bool) (h : hamming_close_skew_system r v w) :
    k ≤ 2 ^ r := by
  have _ := hr
  have hinj : Function.Injective v := by
    intro i j hij
    rcases h with ⟨-, hfar, hskew⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h1 := hfar j
      have h2 := hskew j i hlt
      rw [← hij] at h1
      omega
    · exact heq
    · have h1 := hfar i
      have h2 := hskew i j hgt
      rw [hij] at h1
      omega
  let A := Finset.image v (Finset.univ : Finset (Fin k))
  let B := Finset.image (op_1859_close_skew_n_eq_r_succ_notVec ∘ v) (Finset.univ : Finset (Fin k))
  have hA_card : A.card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hB_card : B.card = k := by
    have hinj2 : Function.Injective (op_1859_close_skew_n_eq_r_succ_notVec ∘ v) :=
      op_1859_close_skew_n_eq_r_succ_notVec_injective.comp hinj
    rw [Finset.card_image_of_injective _ hinj2, Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, -, rfl⟩
    intro heq
    rcases h with ⟨hclose, -, -⟩
    have hd := hclose j i
    have heq_dist : hammingDist (v j) (v i) = r + 1 := by
      rw [heq]
      dsimp [Function.comp]
      exact op_1859_close_skew_n_eq_r_succ_hammingDist_notVec (v j)
    omega
  have h_union_le : (A ∪ B).card ≤ Fintype.card (Fin (r + 1) → Bool) := by
    exact Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint hdisj, hA_card, hB_card] at h_union_le
  have h_total : Fintype.card (Fin (r + 1) → Bool) = 2 ^ (r + 1) := by
    simp
  rw [h_total, pow_succ, mul_two] at h_union_le
  omega
