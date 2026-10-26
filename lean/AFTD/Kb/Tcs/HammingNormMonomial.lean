import AFTD.Prelude
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.Tcs.G

/-!
# hamming_norm_monomial

Topic: information   Node: f699b8f88a70

Provenance: helper lemma. arXiv:2610.29807, Lemma 3.2: Some Results on the Weight Spectrum of Binary Reed-Muller Codes RM(m-7,m)

For any natural number s and any finite subset T of Fin s, the Hamming norm of the coordinate monomial monomial T as a function from (Fin s → ZMod 2) to ZMod 2 is equal to 2 ^ (s - T.card).
-/

lemma hamming_norm_monomial_ne_zero_iff {s : ℕ} (T : Finset (Fin s)) (x : Fin s → ZMod 2) :
    monomial T x ≠ 0 ↔ ∀ i ∈ T, x i = 1 := by
  change (∏ i ∈ T, x i) ≠ 0 ↔ ∀ i ∈ T, x i = 1
  rw [Finset.prod_ne_zero_iff]
  simp_rw [show ∀ y : ZMod 2, y ≠ 0 ↔ y = 1 from fun y => by revert y; decide]

def hamming_norm_monomial_equiv {s : ℕ} (T : Finset (Fin s)) :
    {x : Fin s → ZMod 2 // ∀ i ∈ T, x i = 1} ≃ ({j : Fin s // j ∉ T} → ZMod 2) where
  toFun x j := x.1 j.1
  invFun g := ⟨fun i => if h : i ∈ T then 1 else g ⟨i, h⟩, fun i hi => by simp [hi]⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext i
    dsimp
    split_ifs with hi
    · exact (hx i hi).symm
    · rfl
  right_inv := by
    intro g
    ext ⟨j, hj⟩
    dsimp
    simp [hj]

/-- The Hamming norm of a coordinate monomial indexed by T in s variables is 2^(s - |T|). -/
theorem hamming_norm_monomial {s : ℕ} (T : Finset (Fin s)) :
    hammingNorm (monomial T : (Fin s → ZMod 2) → ZMod 2) = 2 ^ (s - T.card) := by
  change (Finset.filter (fun x => monomial T x ≠ 0) Finset.univ).card = 2 ^ (s - T.card)
  have h_filt : (Finset.filter (fun x => monomial T x ≠ 0) Finset.univ) =
      Finset.filter (fun x => ∀ i ∈ T, x i = 1) Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hamming_norm_monomial_ne_zero_iff T x
  rw [h_filt]
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (hamming_norm_monomial_equiv T)]
  rw [Fintype.card_fun]
  have h1 : Fintype.card (ZMod 2) = 2 := by simp
  have h2 : Fintype.card {j : Fin s // j ∉ T} = s - T.card := by
    rw [Fintype.card_subtype]
    have : (Finset.filter (fun j => j ∉ T) Finset.univ) = Finset.univ \ T := by
      ext x
      simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin]
  rw [h1, h2]
