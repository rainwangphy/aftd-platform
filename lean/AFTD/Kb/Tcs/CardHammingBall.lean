import AFTD.Prelude
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.Supp

/-!
# card_hamming_ball

Topic: information   Node: 747bc1e9f66e

Provenance: formalization of a published result. Source: arXiv:2611.18156 Section II

For natural numbers n, q, r with 2 ≤ q and r ≤ n, and any x : Fin n → Fin q, the cardinality of the Hamming ball of radius r centered at x is ∑ i ∈ Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i.
-/

set_option linter.unusedVariables false

open Finset

def card_hamming_ball_toWord {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n))
    (g : ∀ j : S, {v : Fin q // v ≠ x j.val}) : Fin n → Fin q :=
  fun j => if hj : j ∈ S then (g ⟨j, hj⟩).val else x j

lemma card_hamming_ball_toWord_inj {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n)) :
    Function.Injective (card_hamming_ball_toWord x S) := by
  intro g1 g2 h
  funext ⟨j, hj⟩
  apply Subtype.ext
  have := congr_fun h j
  dsimp [card_hamming_ball_toWord] at this
  simp [hj] at this
  exact this

lemma card_hamming_ball_toWord_mem_fiber {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n))
    (g : ∀ j : S, {v : Fin q // v ≠ x j.val}) :
    filter (fun j => x j ≠ card_hamming_ball_toWord x S g j) univ = S := by
  ext j
  simp only [mem_filter, mem_univ, true_and]
  dsimp [card_hamming_ball_toWord]
  split_ifs with hj
  · simp [(g ⟨j, hj⟩).property.symm, hj]
  · simp [hj]

lemma card_hamming_ball_mem_fiber_eq_toWord {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n))
    (y : Fin n → Fin q) (hy : filter (fun j => x j ≠ y j) univ = S) :
    ∃ g : ∀ j : S, {v : Fin q // v ≠ x j.val}, card_hamming_ball_toWord x S g = y := by
  have hyS : ∀ j ∈ S, x j ≠ y j := by
    intro j hj
    have : j ∈ filter (fun j => x j ≠ y j) univ := by rw [hy]; exact hj
    simp at this
    exact this
  have hyNotS : ∀ j ∉ S, x j = y j := by
    intro j hj
    have : j ∉ filter (fun j => x j ≠ y j) univ := by rw [hy]; exact hj
    simp at this
    exact this
  refine ⟨fun ⟨j, hj⟩ => ⟨y j, ?_⟩, ?_⟩
  · exact (hyS j hj).symm
  · funext j
    dsimp [card_hamming_ball_toWord]
    split_ifs with hj
    · rfl
    · exact (hyNotS j hj)

lemma card_hamming_ball_card_fiber_supp {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n)) :
    (filter (fun (y : Fin n → Fin q) => filter (fun j => x j ≠ y j) univ = S) univ).card = (q - 1) ^ S.card := by
  have himage : filter (fun (y : Fin n → Fin q) => filter (fun j => x j ≠ y j) univ = S) univ =
      image (card_hamming_ball_toWord x S) univ := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := card_hamming_ball_mem_fiber_eq_toWord x S y hy
      exact ⟨g, hg⟩
    · rintro ⟨g, rfl⟩
      exact card_hamming_ball_toWord_mem_fiber x S g
  rw [himage, card_image_of_injective _ (card_hamming_ball_toWord_inj x S), card_univ]
  have h1 : ∀ j : S, Fintype.card {v : Fin q // v ≠ x j.val} = q - 1 := by
    intro j
    have : Fintype.card {v : Fin q // v ≠ x j.val} = (univ.filter (· ≠ x j.val)).card := by
      rw [← Fintype.card_subtype]
    rw [this]
    have he : univ.filter (· ≠ x j.val) = univ.erase (x j.val) := by
      ext a; simp
    rw [he, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [Fintype.card_pi]
  have : (∏ j : S, Fintype.card { v // v ≠ x ↑j }) = ∏ j : S, (q - 1) := by
    apply Finset.prod_congr rfl
    intro j _
    exact h1 j
  rw [this, Finset.prod_const]
  simp

lemma card_hamming_ball_card_hamming_sphere (n q : ℕ) (x : Fin n → Fin q) (i : ℕ) :
    (filter (fun y => hammingDist x y = i) univ).card = Nat.choose n i * (q - 1) ^ i := by
  let supp : (Fin n → Fin q) → Finset (Fin n) := fun y => filter (fun j => x j ≠ y j) univ
  have hdist : ∀ y, hammingDist x y = (supp y).card := fun y => rfl
  have hmaps : Set.MapsTo supp (filter (fun y => hammingDist x y = i) univ)
      (powersetCard i (univ : Finset (Fin n))) := by
    intro y hy
    rw [mem_coe] at hy ⊢
    rw [mem_powersetCard]
    simp only [subset_univ, true_and]
    rw [mem_filter] at hy
    exact hy.2
  rw [card_eq_sum_card_fiberwise hmaps]
  have hsum : ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
      {y ∈ filter (fun y => hammingDist x y = i) univ | supp y = S}.card =
      ∑ S ∈ powersetCard i (univ : Finset (Fin n)), (q - 1) ^ i := by
    apply sum_congr rfl
    intro S hS
    simp only [mem_powersetCard] at hS
    have heq : {y ∈ filter (fun y => hammingDist x y = i) univ | supp y = S} =
        filter (fun y => supp y = S) univ := by
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, hsupp⟩
        exact hsupp
      · intro hsupp
        refine ⟨?_, hsupp⟩
        change (supp y).card = i
        rw [hsupp, hS.2]
    rw [heq]
    have := card_hamming_ball_card_fiber_supp x S
    rw [← hS.2]
    exact this
  rw [hsum, sum_const, smul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin]

/-- Cardinality of a Hamming ball of radius r in (Fin n → Fin q). -/
theorem card_hamming_ball (n q r : ℕ) (hq : 2 ≤ q) (hr : r ≤ n) (x : Fin n → Fin q) :
    (hamming_ball r x).card = ∑ i ∈ Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i := by
  have hmaps : Set.MapsTo (hammingDist x) (hamming_ball r x) (Finset.range (r + 1)) := by
    intro y hy
    rw [Finset.mem_coe] at hy ⊢
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    simp [hamming_ball] at hy
    exact hy
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hsum : ∑ i ∈ Finset.range (r + 1), {y ∈ hamming_ball r x | hammingDist x y = i}.card =
      ∑ i ∈ Finset.range (r + 1), (Finset.filter (fun y => hammingDist x y = i) Finset.univ).card := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy_ball, heq⟩; exact heq
    · intro heq
      refine ⟨?_, heq⟩
      simp [hamming_ball, heq, hi]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact card_hamming_ball_card_hamming_sphere n q x i
