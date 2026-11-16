import AFTD.Prelude
import AFTD.Kb.Tcs.HammingRing
import AFTD.Kb.Tcs.G

/-!
# card_hamming_ring

Topic: information   Node: 0ac2d82150fb

Provenance: formalization of a published result. Source: arXiv:2611.18156 Definition III.1

For natural numbers n, q, c, c' with 2 ≤ q and c + c' ≤ n, and any x : Fin n → Fin q, the cardinality of the (c, c') Hamming ring centered at x is ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j.
-/

private def card_hamming_ring_diffSet {n q : ℕ} (x y : Fin n → Fin q) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)

private def card_hamming_ring_piEquiv {n q : ℕ} (t : Fin n → Finset (Fin q)) :
    {y : Fin n → Fin q // ∀ i, y i ∈ t i} ≃ ((i : Fin n) → {a : Fin q // a ∈ t i}) where
  toFun y i := ⟨y.1 i, y.2 i⟩
  invFun g := ⟨fun i => (g i).1, fun i => (g i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card_hamming_ring_filter_diffSet {n q : ℕ} (x : Fin n → Fin q) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun y : Fin n → Fin q => card_hamming_ring_diffSet x y = S)).card
      = (q - 1) ^ S.card := by
  classical
  let t : Fin n → Finset (Fin q) :=
    fun i => if i ∈ S then Finset.univ.filter (fun a => a ≠ x i) else {x i}
  have hset : Finset.univ.filter (fun y : Fin n → Fin q => card_hamming_ring_diffSet x y = S)
      = Finset.univ.filter (fun y : Fin n → Fin q => ∀ i, y i ∈ t i) := by
    apply Finset.filter_congr
    intro y _
    constructor
    · intro hy i
      by_cases hi : i ∈ S
      · have hmem : i ∈ card_hamming_ring_diffSet x y := by rw [hy]; exact hi
        simp only [card_hamming_ring_diffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        simp only [t, if_pos hi, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hmem.symm
      · have hmem : i ∉ card_hamming_ring_diffSet x y := by rw [hy]; exact hi
        simp only [card_hamming_ring_diffSet, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hmem
        simp only [t, if_neg hi, Finset.mem_singleton]
        exact hmem.symm
    · intro hy
      ext i
      simp only [card_hamming_ring_diffSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hmem := hy i
      by_cases hi : i ∈ S
      · have hyi : y i ≠ x i := by simpa [t, hi] using hmem
        exact ⟨fun _ => hi, fun _ => hyi.symm⟩
      · have hyi : y i = x i := by simpa [t, hi] using hmem
        exact ⟨fun h => absurd hyi.symm h, fun h => absurd h hi⟩
  have hcard : (Finset.univ.filter (fun y : Fin n → Fin q => ∀ i, y i ∈ t i)).card
      = ∏ i, (t i).card := by
    rw [← Fintype.card_subtype (fun y : Fin n → Fin q => ∀ i, y i ∈ t i)]
    rw [Fintype.card_congr (card_hamming_ring_piEquiv t), Fintype.card_pi]
    simp
  have hprod : (∏ i, (t i).card) = (q - 1) ^ S.card := by
    have hterm : ∀ i, (t i).card = if i ∈ S then q - 1 else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [t, if_pos hi]
        rw [show Finset.univ.filter (fun a : Fin q => a ≠ x i) = Finset.univ.erase (x i) by
          ext a; simp]
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · simp [t, hi]
    rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_ite_mem]
    simp
  rw [hset, hcard, hprod]

private lemma card_hamming_ring_sphere {n q : ℕ} (j : ℕ) (x : Fin n → Fin q) :
    (Finset.univ.filter (fun y : Fin n → Fin q => hammingDist x y = j)).card
      = Nat.choose n j * (q - 1) ^ j := by
  classical
  have hset : Finset.univ.filter (fun y : Fin n → Fin q => hammingDist x y = j)
      = (Finset.univ.powersetCard j).biUnion
          (fun S => Finset.univ.filter (fun y : Fin n → Fin q => card_hamming_ring_diffSet x y = S)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_powersetCard]
    constructor
    · intro h
      have hd : hammingDist x y = (card_hamming_ring_diffSet x y).card := rfl
      exact ⟨card_hamming_ring_diffSet x y, ⟨Finset.subset_univ _, by rw [← hd, h]⟩, rfl⟩
    · rintro ⟨S, ⟨-, hS⟩, hEq⟩
      have hd : hammingDist x y = (card_hamming_ring_diffSet x y).card := rfl
      rw [hd, hEq, hS]
  rw [hset, Finset.card_biUnion]
  · trans ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, (q - 1) ^ j
    · apply Finset.sum_congr rfl
      intro S hS
      rw [card_hamming_ring_filter_diffSet]
      rw [(Finset.mem_powersetCard.mp hS).2]
    · rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro S _ T _ hST
    change Disjoint (Finset.univ.filter (fun y : Fin n → Fin q => card_hamming_ring_diffSet x y = S))
      (Finset.univ.filter (fun y : Fin n → Fin q => card_hamming_ring_diffSet x y = T))
    rw [Finset.disjoint_left]
    intro y hyS hyT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyS hyT
    exact hST (hyS.symm.trans hyT)

/-- Cardinality of a (c, c') Hamming ring in (Fin n → Fin q). -/
theorem card_hamming_ring (n q c c' : ℕ) (hq : 2 ≤ q) (hc : c + c' ≤ n) (x : Fin n → Fin q) :
    (hamming_ring c c' x).card = ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j := by
  classical
  have _hq := hq
  have _hc := hc
  have hset : hamming_ring c c' x = (Finset.Icc (c + 1) (c + c')).biUnion
      (fun j => Finset.univ.filter (fun y : Fin n → Fin q => hammingDist x y = j)) := by
    ext y
    simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hammingDist x y, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
  rw [hset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact card_hamming_ring_sphere j x
  · intro j _ k _ hjk
    change Disjoint (Finset.univ.filter (fun y : Fin n → Fin q => hammingDist x y = j))
      (Finset.univ.filter (fun y : Fin n → Fin q => hammingDist x y = k))
    rw [Finset.disjoint_left]
    intro y hj hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
    exact hjk (hj.symm.trans hk)
