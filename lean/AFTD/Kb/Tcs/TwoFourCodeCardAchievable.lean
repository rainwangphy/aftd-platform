import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoFourCode

/-!
# two_four_code_card_achievable

Topic: information   Node: 7266289a70d5

Provenance: helper lemma. step towards op_491_threshold_le

For every alphabet size $q \ge 2$ and every length $n$, there is a $\{2,4\}$-code $C \subseteq (\mathrm{Fin}\, n \to \mathrm{Fin}\, q)$ of cardinality exactly $1 + \binom{n}{2}$: the zero word together with the words carrying a fixed nonzero symbol on the two positions of some 2-element subset of $\{1,\dots,n\}$. This is equation (1) of arXiv:2610.30613, the lower-bound half of $A_q(n,\{2,4\}) = 1 + \binom{n}{2}$, and it holds for every $n$, with no threshold.
-/

open Finset

def two_four_code_card_achievable_z {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨0, by omega⟩
def two_four_code_card_achievable_a {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨1, by omega⟩

lemma two_four_code_card_achievable_haz {q : ℕ} (hq : 2 ≤ q) :
    two_four_code_card_achievable_a hq ≠ two_four_code_card_achievable_z hq := by
  intro h
  have := congr_arg Fin.val h
  cases this

def two_four_code_card_achievable_w {n q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin n)) : Fin n → Fin q :=
  fun i => if i ∈ S then two_four_code_card_achievable_a hq else two_four_code_card_achievable_z hq

lemma two_four_code_card_achievable_w_inj {n q : ℕ} (hq : 2 ≤ q) (S T : Finset (Fin n))
    (h : two_four_code_card_achievable_w hq S = two_four_code_card_achievable_w hq T) : S = T := by
  ext i
  have hi := congr_fun h i
  dsimp [two_four_code_card_achievable_w] at hi
  by_cases hSi : i ∈ S <;> by_cases hTi : i ∈ T
  · simp [hSi, hTi]
  · rw [if_pos hSi, if_neg hTi] at hi
    exact (two_four_code_card_achievable_haz hq hi).elim
  · rw [if_neg hSi, if_pos hTi] at hi
    exact (two_four_code_card_achievable_haz hq hi.symm).elim
  · simp [hSi, hTi]

lemma two_four_code_card_achievable_zero_not_mem_image {n q : ℕ} (hq : 2 ≤ q) :
    (fun _ : Fin n => two_four_code_card_achievable_z hq) ∉
      (powersetCard 2 (univ : Finset (Fin n))).image (two_four_code_card_achievable_w hq) := by
  intro hmem
  rw [mem_image] at hmem
  rcases hmem with ⟨S, hS, hS_eq⟩
  rw [mem_powersetCard] at hS
  have hS_card : S.card = 2 := hS.2
  have hSne : S.Nonempty := by
    rw [← card_pos]
    omega
  rcases hSne with ⟨i, hi⟩
  have hi_eq := congr_fun hS_eq i
  dsimp [two_four_code_card_achievable_w] at hi_eq
  rw [if_pos hi] at hi_eq
  exact two_four_code_card_achievable_haz hq hi_eq

lemma two_four_code_card_achievable_inter_card_le_one_of_card_two {α : Type*} [DecidableEq α] {s t : Finset α}
    (hs : s.card = 2) (ht : t.card = 2) (hne : s ≠ t) :
    (s ∩ t).card ≤ 1 := by
  by_contra! h
  have h_le : (s ∩ t).card ≤ s.card := card_le_card inter_subset_left
  have h_eq : (s ∩ t).card = s.card := by omega
  have : s ∩ t = s := eq_of_subset_of_card_le inter_subset_left (by rw [h_eq])
  have h_sub : s ⊆ t := by
    rw [← this]
    exact inter_subset_right
  have : s = t := eq_of_subset_of_card_le h_sub (by rw [hs, ht])
  exact hne this

lemma two_four_code_card_achievable_filter_ne_w_w {n q : ℕ} (hq : 2 ≤ q) (S T : Finset (Fin n)) :
    (univ.filter (fun i => two_four_code_card_achievable_w hq S i ≠ two_four_code_card_achievable_w hq T i)) =
      (S \ T) ∪ (T \ S) := by
  ext i
  rw [mem_filter]
  simp only [mem_univ, true_and, mem_union, mem_sdiff]
  dsimp [two_four_code_card_achievable_w]
  by_cases hSi : i ∈ S <;> by_cases hTi : i ∈ T
  · simp [hSi, hTi]
  · rw [if_pos hSi, if_neg hTi]
    simp [hSi, hTi, two_four_code_card_achievable_haz hq]
  · rw [if_neg hSi, if_pos hTi]
    simp [hSi, hTi, (two_four_code_card_achievable_haz hq).symm]
  · simp [hSi, hTi]

lemma two_four_code_card_achievable_dist_w_w {n q : ℕ} (hq : 2 ≤ q) (S T : Finset (Fin n))
    (hS : S.card = 2) (hT : T.card = 2) (hST : S ≠ T) :
    hammingDist (two_four_code_card_achievable_w hq S) (two_four_code_card_achievable_w hq T) = 2 ∨
    hammingDist (two_four_code_card_achievable_w hq S) (two_four_code_card_achievable_w hq T) = 4 := by
  change (univ.filter (fun i => two_four_code_card_achievable_w hq S i ≠ two_four_code_card_achievable_w hq T i)).card = 2 ∨
         (univ.filter (fun i => two_four_code_card_achievable_w hq S i ≠ two_four_code_card_achievable_w hq T i)).card = 4
  rw [two_four_code_card_achievable_filter_ne_w_w]
  rw [card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 : (S \ T).card + (S ∩ T).card = 2 := by
    rw [card_sdiff_add_card_inter, hS]
  have h2 : (T \ S).card + (S ∩ T).card = 2 := by
    rw [inter_comm, card_sdiff_add_card_inter, hT]
  have h3 : (S ∩ T).card ≤ 1 := two_four_code_card_achievable_inter_card_le_one_of_card_two hS hT hST
  omega

lemma two_four_code_card_achievable_dist_zero_w {n q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin n)) (hS : S.card = 2) :
    hammingDist (fun _ : Fin n => two_four_code_card_achievable_z hq) (two_four_code_card_achievable_w hq S) = 2 := by
  change (univ.filter (fun i => (fun _ : Fin n => two_four_code_card_achievable_z hq) i ≠ two_four_code_card_achievable_w hq S i)).card = 2
  have : (univ.filter (fun i => (fun _ : Fin n => two_four_code_card_achievable_z hq) i ≠ two_four_code_card_achievable_w hq S i)) = S := by
    ext i
    rw [mem_filter]
    simp only [mem_univ, true_and]
    dsimp [two_four_code_card_achievable_w]
    split_ifs with hi
    · simp [hi, (two_four_code_card_achievable_haz hq).symm]
    · simp [hi]
  rw [this, hS]

/-- The extremal {2,4}-code: the zero word plus one indicator word per 2-subset of the coordinates, of cardinality 1 + C(n,2). -/
theorem two_four_code_card_achievable (q n : ℕ) (hq : 2 ≤ q) :
    ∃ C : Finset (Fin n → Fin q),
      C.card = 1 + n.choose 2 ∧ is_two_four_code (C : Set (Fin n → Fin q)) := by
  open Finset in
  classical
  let z : Fin n → Fin q := fun _ => two_four_code_card_achievable_z hq
  let C : Finset (Fin n → Fin q) :=
    insert z ((powersetCard 2 (univ : Finset (Fin n))).image (two_four_code_card_achievable_w hq))
  use C
  constructor
  · dsimp [C]
    rw [card_insert_of_notMem (two_four_code_card_achievable_zero_not_mem_image hq)]
    rw [card_image_of_injective _ (fun _ _ => two_four_code_card_achievable_w_inj hq _ _)]
    rw [card_powersetCard, card_univ, Fintype.card_fin]
    omega
  · intro x hx y hy hxy
    rw [Finset.mem_coe, mem_insert, mem_image] at hx hy
    rcases hx with rfl | ⟨S, hS, rfl⟩
    · rcases hy with rfl | ⟨T, hT, rfl⟩
      · contradiction
      · rw [mem_powersetCard] at hT
        exact Or.inl (two_four_code_card_achievable_dist_zero_w hq T hT.2)
    · rcases hy with rfl | ⟨T, hT, rfl⟩
      · rw [mem_powersetCard] at hS
        rw [hammingDist_comm]
        exact Or.inl (two_four_code_card_achievable_dist_zero_w hq S hS.2)
      · rw [mem_powersetCard] at hS hT
        have hST : S ≠ T := by
          intro hST
          apply hxy
          rw [hST]
        exact two_four_code_card_achievable_dist_w_w hq S T hS.2 hT.2 hST
