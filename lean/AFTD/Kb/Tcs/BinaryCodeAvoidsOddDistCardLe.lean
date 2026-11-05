import AFTD.Prelude

/-!
# binary_code_avoids_odd_dist_card_le

Topic: combinatorics   Node: 3dd15747b605

Provenance: helper lemma. arXiv:2611.04523, Proposition 3.1

Let n ≥ 1 and 1 ≤ d ≤ n. Every finite set of binary words F : Finset (Fin n → Fin 2) such that no two elements have Hamming distance d satisfies F.card ≤ 2 ^ (n - 1).
-/

def binary_code_avoids_odd_dist_card_le_shift (n d : ℕ) : Fin n → Fin 2 :=
  fun i => if (i : ℕ) < d then 1 else 0

lemma binary_code_avoids_odd_dist_card_le_card_shift (n d : ℕ) (hdn : d ≤ n) :
    (Finset.univ.filter (fun i : Fin n => binary_code_avoids_odd_dist_card_le_shift n d i ≠ 0)).card = d := by
  have h1 : (Finset.univ.filter (fun i : Fin n => binary_code_avoids_odd_dist_card_le_shift n d i ≠ 0)) =
            Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [binary_code_avoids_odd_dist_card_le_shift]
    split_ifs with h <;> simp [h]
  rw [h1]
  have h2 : Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) =
      Finset.map ⟨Fin.castLE hdn, Fin.castLE_injective hdn⟩ Finset.univ := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h
      refine ⟨⟨i, h⟩, ?_⟩
      ext
      rfl
    · rintro ⟨⟨j, hj⟩, h⟩
      have : j = i := by injection h
      rw [← this]
      exact hj
  rw [h2, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma binary_code_avoids_odd_dist_card_le_hammingDist_shift (n d : ℕ) (hdn : d ≤ n) (x : Fin n → Fin 2) :
    hammingDist x (x + binary_code_avoids_odd_dist_card_le_shift n d) = d := by
  have h : hammingDist x (x + binary_code_avoids_odd_dist_card_le_shift n d) =
           (Finset.univ.filter (fun i : Fin n => binary_code_avoids_odd_dist_card_le_shift n d i ≠ 0)).card := by
    unfold hammingDist
    congr 1
    ext i
    simp
  rw [h, binary_code_avoids_odd_dist_card_le_card_shift n d hdn]

/-- A binary code in {0,1}^n avoiding a distance d with 1 ≤ d ≤ n has cardinality at most 2^(n-1). -/
theorem binary_code_avoids_odd_dist_card_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n) (F : Finset (Fin n → Fin 2)) (hF : ∀ x ∈ F, ∀ y ∈ F, hammingDist x y ≠ d) : F.card ≤ 2 ^ (n - 1) := by
  let v := binary_code_avoids_odd_dist_card_le_shift n d
  let f : (Fin n → Fin 2) ↪ (Fin n → Fin 2) := ⟨fun x => x + v, add_left_injective v⟩
  let F' := F.map f
  have hdisj : Disjoint F F' := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rcases Finset.mem_map.mp hy2 with ⟨x, hx, rfl⟩
    have hd_eq := binary_code_avoids_odd_dist_card_le_hammingDist_shift n d hdn x
    exact hF x hx (x + v) hy1 hd_eq
  have h_card_eq : F'.card = F.card := Finset.card_map f
  have h_union : (F ∪ F').card = F.card + F'.card := Finset.card_union_of_disjoint hdisj
  have h_le_univ : (F ∪ F').card ≤ Fintype.card (Fin n → Fin 2) := Finset.card_le_univ (F ∪ F')
  have h_total : Fintype.card (Fin n → Fin 2) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_sum : F.card + F.card ≤ 2 ^ n := by
    omega
  have h_pow : 2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
  rw [h_pow, pow_succ] at h_sum
  omega
