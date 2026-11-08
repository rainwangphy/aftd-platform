import AFTD.Prelude
import AFTD.Kb.Tcs.SumsetRepCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SumsetFinsetSortedVector
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.SumsetSumVectorsFinset
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G

/-!
# sumset_rep_count_le_choose_mul_choose

Topic: combinatorics   Node: 9dd36dd8d34f

Provenance: formalization of a published result. Source: arXiv:2611.07303 Sec. 5.2, Question 3

For any k ≥ 1, h, q, and integer s, the representation count ν_q(s) is bounded above by (h + k choose k - 1) * (q choose k - 1).
-/

open Finset

private lemma sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb {k : ℕ} (A : Finset ℤ) (hA : A.card = k) :
    sumset_finset_sorted_vector k A = ⇑(A.orderEmbOfFin hA) := by
  funext i; rw [sumset_finset_sorted_vector, dif_pos hA]

private lemma sumset_rep_count_le_choose_mul_choose_sv_erase_eq {n : ℕ} (A : Finset ℤ) (hA : A.card = n + 1) (i : Fin (n+1)) :
    sumset_finset_sorted_vector n (A.erase (A.orderEmbOfFin hA i)) =
      fun j : Fin n => A.orderEmbOfFin hA (i.succAbove j) := by
  have h1 : A.orderEmbOfFin hA i ∈ A := Finset.orderEmbOfFin_mem A hA i
  have hB : (A.erase (A.orderEmbOfFin hA i)).card = n := by
    rw [Finset.card_erase_of_mem h1, hA]; simp
  rw [sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb _ hB]
  refine (Finset.orderEmbOfFin_unique (s := A.erase (A.orderEmbOfFin hA i))
    (f := fun j : Fin n => A.orderEmbOfFin hA (i.succAbove j)) hB ?_ ?_).symm
  · intro j; rw [Finset.mem_erase]
    exact ⟨fun h => (Fin.succAbove_ne i j) ((A.orderEmbOfFin hA).injective h),
      Finset.orderEmbOfFin_mem A hA (i.succAbove j)⟩
  · exact (A.orderEmbOfFin hA).strictMono.comp (Fin.succAboveOrderEmb i).strictMono

private lemma sumset_rep_count_le_choose_mul_choose_dot_succAbove {n : ℕ} (x : Fin (n+1) → ℤ) (A : Finset ℤ) (hA : A.card = n+1) (i : Fin (n+1)) :
    dotProduct x (sumset_finset_sorted_vector (n+1) A) =
      x i * sumset_finset_sorted_vector (n+1) A i +
      dotProduct (fun j : Fin n => x (i.succAbove j))
        (sumset_finset_sorted_vector n (A.erase (sumset_finset_sorted_vector (n+1) A i))) := by
  rw [show sumset_finset_sorted_vector (n+1) A = ⇑(A.orderEmbOfFin hA) from sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb A hA,
    show sumset_finset_sorted_vector n (A.erase (A.orderEmbOfFin hA i)) =
      fun j : Fin n => A.orderEmbOfFin hA (i.succAbove j) from sumset_rep_count_le_choose_mul_choose_sv_erase_eq A hA i]
  simp only [dotProduct]; rw [Fin.sum_univ_succAbove _ i]

private lemma sumset_rep_count_le_choose_mul_choose_sum_vec_nonneg {k h : ℕ} {x : Fin k → ℤ} (hx : x ∈ sumset_sum_vectors_finset (h+1) k) (i : Fin k) : 0 ≤ x i := by
  simp only [sumset_sum_vectors_finset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range] at hx
  rcases hx.1 i with ⟨m, -, hm⟩
  rw [← hm]
  exact Nat.cast_nonneg m

private lemma sumset_rep_count_le_choose_mul_choose_sum_vec_sum {k h : ℕ} {x : Fin k → ℤ} (hx : x ∈ sumset_sum_vectors_finset (h+1) k) : ∑ i, x i = ((h:ℤ) + 1) := by
  simp only [sumset_sum_vectors_finset, Finset.mem_filter] at hx; rw [hx.2]; push_cast; ring

private lemma sumset_rep_count_le_choose_mul_choose_sum_vec_exists_pos {k h : ℕ} {x : Fin k → ℤ} (hx : x ∈ sumset_sum_vectors_finset (h+1) k) : ∃ i, 0 < x i := by
  by_contra hcon; push Not at hcon
  have h1 : ∑ i, x i ≤ 0 := by
    have h2 := Finset.sum_nonpos (s := (Finset.univ : Finset (Fin k))) (f := x) (fun i _ => hcon i)
    simpa using h2
  have h2 := sumset_rep_count_le_choose_mul_choose_sum_vec_sum hx; linarith

private lemma sumset_rep_count_le_choose_mul_choose_filter_card_le_choose {n : ℕ} (x : Fin (n+1) → ℤ) (i : Fin (n+1))
    (hi : x i ≠ 0) (q : ℕ) (s : ℤ) :
    (((Finset.Icc 1 (q:ℤ)).powersetCard (n+1)).filter
      (fun A => dotProduct x (sumset_finset_sorted_vector (n+1) A) = s)).card ≤ Nat.choose q n := by
  classical
  set Z := (Finset.Icc 1 (q:ℤ)).powersetCard n with hZ
  have hZcard : Z.card = Nat.choose q n := by
    rw [hZ, Finset.card_powersetCard, Int.card_Icc]
    have h1 : (q:ℤ) + 1 - 1 = (q:ℤ) := by ring
    rw [h1, Int.toNat_natCast]
  let F := ((Finset.Icc 1 (q:ℤ)).powersetCard (n+1)).filter
      (fun A => dotProduct x (sumset_finset_sorted_vector (n+1) A) = s)
  let g : Finset ℤ → Finset ℤ := fun A => A.erase (sumset_finset_sorted_vector (n+1) A i)
  have hmaps : Set.MapsTo g ↑F ↑Z := by
    intro A hA
    simp only [Finset.mem_coe, F, Finset.mem_filter] at hA
    obtain ⟨hAY, -⟩ := hA
    rw [Finset.mem_powersetCard] at hAY
    show g A ∈ Z
    rw [hZ, Finset.mem_powersetCard]
    refine ⟨fun b hb => hAY.1 (Finset.mem_of_mem_erase hb), ?_⟩
    have hmemv : sumset_finset_sorted_vector (n+1) A i ∈ A := by
      rw [sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb A hAY.2]; exact Finset.orderEmbOfFin_mem A hAY.2 i
    show (A.erase (sumset_finset_sorted_vector (n+1) A i)).card = n
    rw [Finset.card_erase_of_mem hmemv, hAY.2]; simp
  have hinj : Set.InjOn g ↑F := by
    intro A hA B hB heq
    simp only [Finset.mem_coe, F, Finset.mem_filter] at hA hB
    obtain ⟨hAY, hAP⟩ := hA
    obtain ⟨hBY, hBP⟩ := hB
    rw [Finset.mem_powersetCard] at hAY hBY
    have heq2 : A.erase (sumset_finset_sorted_vector (n+1) A i) =
        B.erase (sumset_finset_sorted_vector (n+1) B i) := heq
    have dA := sumset_rep_count_le_choose_mul_choose_dot_succAbove x A hAY.2 i
    have dB := sumset_rep_count_le_choose_mul_choose_dot_succAbove x B hBY.2 i
    rw [dA] at hAP
    rw [dB] at hBP
    rw [heq2] at hAP
    have hkey : x i * sumset_finset_sorted_vector (n+1) A i =
        x i * sumset_finset_sorted_vector (n+1) B i := by linarith
    have hab : sumset_finset_sorted_vector (n+1) A i =
        sumset_finset_sorted_vector (n+1) B i := mul_left_cancel₀ hi hkey
    have hAm : sumset_finset_sorted_vector (n+1) A i ∈ A := by
      rw [sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb A hAY.2]; exact Finset.orderEmbOfFin_mem A hAY.2 i
    have hBm : sumset_finset_sorted_vector (n+1) B i ∈ B := by
      rw [sumset_rep_count_le_choose_mul_choose_sv_eq_orderEmb B hBY.2]; exact Finset.orderEmbOfFin_mem B hBY.2 i
    rw [← Finset.insert_erase hAm, ← Finset.insert_erase hBm, ← heq2, hab]
  have h := Finset.card_le_card_of_injOn g hmaps hinj
  rw [hZcard] at h
  exact h

/-- Universal upper bound on sumset representation count ν_q(s) ≤ (h+k choose k-1) * (q choose k-1). -/
theorem sumset_rep_count_le_choose_mul_choose (k h q : ℕ) (hk : 1 ≤ k) (s : ℤ) :
    sumset_rep_count h k q s ≤ Nat.choose (h + k) (k - 1) * Nat.choose q (k - 1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have he : (n+1) - 1 = n := by omega
  rw [he]
  have hsum : ∀ x ∈ sumset_sum_vectors_finset (h+1) (n+1), ∑ i, (x i).toNat = h+1 := by
    intro x hx
    have h2 : ∀ i, 0 ≤ x i := fun i => sumset_rep_count_le_choose_mul_choose_sum_vec_nonneg hx i
    have e2 : ((∑ i, (x i).toNat : ℕ) : ℤ) = ∑ i, x i := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h2 i)
    have h3 := e2.trans (sumset_rep_count_le_choose_mul_choose_sum_vec_sum hx)
    omega
  have hsub : (sumset_sum_vectors_finset (h+1) (n+1)).card ≤ (h + (n+1)).choose n := by
    set S := sumset_sum_vectors_finset (h+1) (n+1)
    let g : S → Sym (Fin (n+1)) (h+1) := fun x =>
      (Sym.equivNatSumOfFintype (Fin (n+1)) (h+1)).symm ⟨fun i => (x.1 i).toNat, hsum x.1 x.2⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      have hh := congrArg (fun z => ((Sym.equivNatSumOfFintype (Fin (n+1)) (h+1)) z : Fin (n+1) → ℕ)) hxy
      simp only [g, Equiv.apply_symm_apply] at hh
      refine Subtype.ext (funext fun i => ?_)
      have h1 := congrFun hh i
      have hx' := sumset_rep_count_le_choose_mul_choose_sum_vec_nonneg x.2 i
      have hy' := sumset_rep_count_le_choose_mul_choose_sum_vec_nonneg y.2 i
      have hc : ((x.1 i).toNat : ℤ) = ((y.1 i).toNat : ℤ) := by rw [h1]
      rw [Int.toNat_of_nonneg hx', Int.toNat_of_nonneg hy'] at hc
      exact hc
    calc S.card = Fintype.card S := (Fintype.card_coe S).symm
      _ ≤ Fintype.card (Sym (Fin (n+1)) (h+1)) := Fintype.card_le_of_injective g hinj
      _ = ((n+1) + (h+1) - 1).choose (h+1) := by rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      _ = (h + (n+1)).choose n := by
          have e1 : (n+1) + (h+1) - 1 = h + (n+1) := by omega
          rw [e1, ← Nat.choose_symm (show h + 1 ≤ h + (n+1) by omega)]
          congr 1
          omega
  have hfiber : ∀ x ∈ sumset_sum_vectors_finset (h+1) (n+1),
      (((Finset.Icc 1 (q:ℤ)).powersetCard (n+1)).filter
        (fun A => dotProduct x (sumset_finset_sorted_vector (n+1) A) = s)).card ≤ Nat.choose q n := by
    intro x hx
    obtain ⟨i, hi⟩ := sumset_rep_count_le_choose_mul_choose_sum_vec_exists_pos hx
    exact sumset_rep_count_le_choose_mul_choose_filter_card_le_choose x i (ne_of_gt hi) q s
  calc sumset_rep_count h (n+1) q s
      = ∑ x ∈ sumset_sum_vectors_finset (h+1) (n+1),
          (((Finset.Icc 1 (q:ℤ)).powersetCard (n+1)).filter
            (fun A => dotProduct x (sumset_finset_sorted_vector (n+1) A) = s)).card := by
        simp only [sumset_rep_count, Finset.card_filter, Finset.sum_product]
    _ ≤ ∑ x ∈ sumset_sum_vectors_finset (h+1) (n+1), Nat.choose q n := Finset.sum_le_sum hfiber
    _ = (sumset_sum_vectors_finset (h+1) (n+1)).card * Nat.choose q n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (h + (n+1)).choose n * Nat.choose q n := Nat.mul_le_mul_right _ hsub
