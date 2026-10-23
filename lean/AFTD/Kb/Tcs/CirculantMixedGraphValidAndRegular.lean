import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid
import AFTD.Kb.Tcs.MixedGraphIsRegular
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# circulant_mixed_graph_valid_and_regular

Topic: graphs   Node: 9e53f3b5cda4

Provenance: helper lemma. step towards mixed_cage_order_one_le

For z ≥ 1 and g ≥ 3, the circulant mixed graph on N = N(z, g) vertices with antipodal edges of jump m = N/2 and arc jumps 1..⌈z/2⌉ and m+1..m+⌊z/2⌋ is valid and (1, z)-regular.
-/

theorem circulant_mixed_graph_valid_and_regular_nat_add_mod_sub (n a z : ℕ) (ha : a < n) (hz : z < n) :
    (a + (n - a + z) % n) % n = z := by
  rcases Nat.lt_or_ge z a with h | h
  · have hmod : (n - a + z) % n = n - a + z := Nat.mod_eq_of_lt (by omega)
    rw [hmod]; have : a + (n - a + z) = z + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hz]
  · have h1 : n - a + z = (z - a) + n := by omega
    rw [h1, Nat.add_mod_right]; have h2 : z - a < n := by omega
    rw [Nat.mod_eq_of_lt h2]; have : a + (z - a) = z := by omega
    rw [this, Nat.mod_eq_of_lt hz]
theorem circulant_mixed_graph_valid_and_regular_nat_sub_add_mod (n a d : ℕ) (ha : a < n) (hd : d < n) :
    (n - a + (a + d) % n) % n = d := by
  rcases Nat.lt_or_ge (a + d) n with h | h
  · rw [Nat.mod_eq_of_lt h]; have : n - a + (a + d) = n + d := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hd]
  · have h2 : (a + d) % n = a + d - n := by rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [h2]; have : n - a + (a + d - n) = d := by omega
    rw [this, Nat.mod_eq_of_lt hd]
theorem circulant_mixed_graph_valid_and_regular_fin_add_sub_cancel {n : ℕ} (x y : Fin n) : x + (y - x) = y := by
  ext; rw [Fin.val_add, Fin.val_sub]; exact circulant_mixed_graph_valid_and_regular_nat_add_mod_sub n x.val y.val x.isLt y.isLt
theorem circulant_mixed_graph_valid_and_regular_fin_add_sub_self_right {n : ℕ} (x d : Fin n) : (x + d) - x = d := by
  ext; rw [Fin.val_sub, Fin.val_add]; exact circulant_mixed_graph_valid_and_regular_nat_sub_add_mod n x.val d.val x.isLt d.isLt
theorem circulant_mixed_graph_valid_and_regular_fin_sub_add_cancel {n : ℕ} (x d : Fin n) : (x - d) + d = x := by
  rw [add_comm]; exact circulant_mixed_graph_valid_and_regular_fin_add_sub_cancel d x
theorem circulant_mixed_graph_valid_and_regular_fin_sub_sub_self {n : ℕ} (x d : Fin n) : x - (x - d) = d := by
  have hx : x = (x - d) + d := (circulant_mixed_graph_valid_and_regular_fin_sub_add_cancel x d).symm
  nth_rewrite 1 [hx]; exact circulant_mixed_graph_valid_and_regular_fin_add_sub_self_right (x - d) d
theorem circulant_mixed_graph_valid_and_regular_fin_val_sub_add_sub {n : ℕ} (x y : Fin n) (hne : x ≠ y) :
    (y - x).val + (x - y).val = n := by
  have h1 := Fin.intCast_val_sub_eq_sub_add_ite y x
  have h2 := Fin.intCast_val_sub_eq_sub_add_ite x y
  have key : ((y - x).val : ℤ) + ((x - y).val : ℤ) = n := by
    rw [h1, h2]
    by_cases hxy : x ≤ y
    · have hyx : ¬ (y ≤ x) := by intro h; exact hne (le_antisymm hxy h)
      rw [if_pos hxy, if_neg hyx]; ring
    · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
      rw [if_neg hxy, if_pos hyx]; ring
  have key' : ((y - x).val + (x - y).val : ℤ) = n := by exact key
  exact_mod_cast key'
theorem circulant_mixed_graph_valid_and_regular_ncard_fin_val_Icc (N a b : ℕ) (hb : b < N) :
    ({d : Fin N | a ≤ d.val ∧ d.val ≤ b} : Set (Fin N)).ncard = b + 1 - a := by
  have hmain : ({d : Fin N | a ≤ d.val ∧ d.val ≤ b} : Set (Fin N)).ncard = (Set.Icc a b : Set ℕ).ncard := by
    apply Set.ncard_congr (f := fun (d : Fin N) (_ : d ∈ {d : Fin N | a ≤ d.val ∧ d.val ≤ b}) => d.val)
    · intro d hd; simp only [Set.mem_setOf_eq, Set.mem_Icc] at hd ⊢; exact hd
    · intro d1 d2 hd1 hd2 heq; exact Fin.ext heq
    · intro k hk; simp only [Set.mem_Icc] at hk
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩; simp only [Set.mem_setOf_eq]; exact hk
  rw [hmain, Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Nat.card_Icc]
theorem circulant_mixed_graph_valid_and_regular_ncard_translate_right (N : ℕ) (x : Fin N) (S : Set (Fin N)) :
    ({y : Fin N | (y - x) ∈ S} : Set (Fin N)).ncard = S.ncard := by
  symm
  apply Set.ncard_congr (f := fun (d : Fin N) (_ : d ∈ S) => x + d)
  · intro d hd; show (x + d - x) ∈ S; rw [circulant_mixed_graph_valid_and_regular_fin_add_sub_self_right]; exact hd
  · intro a b ha hb heq
    calc a = (x + a) - x := (circulant_mixed_graph_valid_and_regular_fin_add_sub_self_right x a).symm
      _ = (x + b) - x := by rw [heq]
      _ = b := circulant_mixed_graph_valid_and_regular_fin_add_sub_self_right x b
  · intro y hy; exact ⟨y - x, hy, circulant_mixed_graph_valid_and_regular_fin_add_sub_cancel x y⟩
theorem circulant_mixed_graph_valid_and_regular_ncard_sub_left (N : ℕ) (x : Fin N) (S : Set (Fin N)) :
    ({y : Fin N | (x - y) ∈ S} : Set (Fin N)).ncard = S.ncard := by
  symm
  apply Set.ncard_congr (f := fun (d : Fin N) (_ : d ∈ S) => x - d)
  · intro d hd; show (x - (x - d)) ∈ S; rw [circulant_mixed_graph_valid_and_regular_fin_sub_sub_self]; exact hd
  · intro a b ha hb heq
    calc a = x - (x - a) := (circulant_mixed_graph_valid_and_regular_fin_sub_sub_self x a).symm
      _ = x - (x - b) := by rw [heq]
      _ = b := circulant_mixed_graph_valid_and_regular_fin_sub_sub_self x b
  · intro y hy; exact ⟨x - y, hy, circulant_mixed_graph_valid_and_regular_fin_sub_sub_self x y⟩

theorem circulant_mixed_graph_valid_and_regular_general (N m z : ℕ) (hz : 1 ≤ z) (hm : z < m) (hNm : N = 2 * m) :
    mixed_graph_is_valid (SimpleGraph.fromRel fun (x y : Fin N) => (y - x).val = m)
      (fun x y => (1 ≤ (y - x).val ∧ (y - x).val ≤ (z + 1) / 2) ∨
        (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + z / 2)) ∧
    mixed_graph_is_regular (SimpleGraph.fromRel fun (x y : Fin N) => (y - x).val = m)
      (fun x y => (1 ≤ (y - x).val ∧ (y - x).val ≤ (z + 1) / 2) ∨
        (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + z / 2)) 1 z := by
  set c1 := (z + 1) / 2 with hc1
  set c2 := z / 2 with hc2
  set E : SimpleGraph (Fin N) := SimpleGraph.fromRel (fun (x y : Fin N) => (y - x).val = m) with hE
  set T : Set (Fin N) := {d : Fin N | 1 ≤ d.val ∧ d.val ≤ c1 ∨ m + 1 ≤ d.val ∧ d.val ≤ m + c2} with hT
  set A : Fin N → Fin N → Prop :=
    (fun x y => (1 ≤ (y - x).val ∧ (y - x).val ≤ c1) ∨ (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + c2)) with hA
  have hc12 : c1 + c2 = z := by omega
  have hmpos : 0 < m := by omega
  have hmN : m < N := by omega
  have hc1z : c1 ≤ z := by omega
  have hc2z : c2 ≤ z := by omega
  have hmc2N : m + c2 < N := by omega
  have hval_self : ∀ w : Fin N, (w - w).val = 0 := by
    intro w
    rw [Fin.val_sub]
    have h : N - w.val + w.val = N := by omega
    rw [h, Nat.mod_self]
  have hTncard : T.ncard = z := by
    have hT_eq : T = {d : Fin N | 1 ≤ d.val ∧ d.val ≤ c1} ∪ {d : Fin N | m + 1 ≤ d.val ∧ d.val ≤ m + c2} := by
      rw [hT]; ext d; simp only [Set.mem_setOf_eq, Set.mem_union]
    have hdisj : Disjoint ({d : Fin N | 1 ≤ d.val ∧ d.val ≤ c1} : Set (Fin N))
        {d : Fin N | m + 1 ≤ d.val ∧ d.val ≤ m + c2} := by
      rw [Set.disjoint_left]; intro d h1 h2
      simp only [Set.mem_setOf_eq] at h1 h2; omega
    rw [hT_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    have hn1 : ({d : Fin N | 1 ≤ d.val ∧ d.val ≤ c1} : Set (Fin N)).ncard = c1 := by
      rw [circulant_mixed_graph_valid_and_regular_ncard_fin_val_Icc N 1 c1 (by omega)]; omega
    have hn2 : ({d : Fin N | m + 1 ≤ d.val ∧ d.val ≤ m + c2} : Set (Fin N)).ncard = c2 := by
      rw [circulant_mixed_graph_valid_and_regular_ncard_fin_val_Icc N (m + 1) (m + c2) (by omega)]; omega
    rw [hn1, hn2, hc12]
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      simp only [hA]
      have h0 := hval_self x
      omega
    · intro x y hAxy
      simp only [hA] at hAxy ⊢
      rcases hAxy with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · have hxy : x ≠ y := by
          intro h; subst h; rw [hval_self x] at hp1; omega
        have hsum := circulant_mixed_graph_valid_and_regular_fin_val_sub_add_sub x y hxy
        have hq : (x - y).val = N - (y - x).val := by omega
        rw [hq]; omega
      · have hxy : x ≠ y := by
          intro h; subst h; rw [hval_self x] at hp1; omega
        have hsum := circulant_mixed_graph_valid_and_regular_fin_val_sub_add_sub x y hxy
        have hq : (x - y).val = N - (y - x).val := by omega
        rw [hq]; omega
    · intro x y hExy
      rw [hE, SimpleGraph.fromRel_adj] at hExy
      simp only [hA]
      rcases hExy with ⟨hne, hp | hp⟩
      · rw [hp]; omega
      · have hsum := circulant_mixed_graph_valid_and_regular_fin_val_sub_add_sub x y hne
        have hq : (y - x).val = m := by omega
        rw [hq]; omega
  · intro x
    have hEadj : ∀ y : Fin N, E.Adj x y ↔ (y - x).val = m := by
      intro y
      rw [hE, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨hne, hp | hp⟩
        · exact hp
        · have hsum := circulant_mixed_graph_valid_and_regular_fin_val_sub_add_sub x y hne; omega
      · intro hp
        refine ⟨?_, Or.inl hp⟩
        intro hxy; rw [hxy] at hp
        have hv := hval_self y; omega
    refine ⟨?_, ?_, ?_⟩
    · have hset : {y : Fin N | E.Adj x y} = {y : Fin N | (y - x) ∈ ({d : Fin N | d.val = m} : Set (Fin N))} := by
        ext y; simp only [Set.mem_setOf_eq]; exact hEadj y
      rw [hset, circulant_mixed_graph_valid_and_regular_ncard_translate_right N x {d : Fin N | d.val = m}]
      have he : ({d : Fin N | d.val = m} : Set (Fin N)) = {d : Fin N | m ≤ d.val ∧ d.val ≤ m} := by
        ext d; simp only [Set.mem_setOf_eq]; omega
      rw [he, circulant_mixed_graph_valid_and_regular_ncard_fin_val_Icc N m m hmN]; omega
    · have hset : {y : Fin N | A x y} = {y : Fin N | (y - x) ∈ T} := by
        ext y; simp only [hA, hT, Set.mem_setOf_eq]
      rw [hset, circulant_mixed_graph_valid_and_regular_ncard_translate_right N x T]; exact hTncard
    · have hset : {y : Fin N | A y x} = {y : Fin N | (x - y) ∈ T} := by
        ext y; simp only [hA, hT, Set.mem_setOf_eq]
      rw [hset, circulant_mixed_graph_valid_and_regular_ncard_sub_left N x T]; exact hTncard

/-- The circulant mixed graph M(z, g) on N(z, g) vertices is valid (loopless, asymmetric arcs, disjoint edge and arc sets) and (1, z)-regular. -/
theorem circulant_mixed_graph_valid_and_regular (z g : ℕ) (hz : 1 ≤ z) (hg : 3 ≤ g) :
    let N := if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1)
    let m := N / 2
    let E := SimpleGraph.fromRel fun (x y : Fin N) => (y - x).val = m
    let A : Fin N → Fin N → Prop := fun x y =>
      (1 ≤ (y - x).val ∧ (y - x).val ≤ (z + 1) / 2) ∨
      (m + 1 ≤ (y - x).val ∧ (y - x).val ≤ m + z / 2)
    mixed_graph_is_valid E A ∧ mixed_graph_is_regular E A 1 z := by
  dsimp only
  set N := (if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1)) with hN
  have hg1 : 2 ≤ g - 1 := by omega
  have hN_even : Even N := by
    by_cases hze : Even z
    · rw [hN]; simp only [hze, if_true]
      exact Even.add (hze.mul_right (g - 1)) even_two
    · rw [hN]; simp only [hze, if_false]
      have hodd : Odd z := Nat.not_even_iff_odd.mp hze
      exact (hodd.add_one).mul_right (g - 1)
  have hN_ge : 2 * (z + 1) ≤ N := by
    by_cases hze : Even z
    · rw [hN]; simp only [hze, if_true]
      have h2 : z * 2 ≤ z * (g - 1) := Nat.mul_le_mul_left z hg1
      omega
    · rw [hN]; simp only [hze, if_false]
      have h2 : (z + 1) * 2 ≤ (z + 1) * (g - 1) := Nat.mul_le_mul_left (z + 1) hg1
      omega
  have hNm : N = 2 * (N / 2) := by
    have h := Nat.div_two_mul_two_of_even hN_even
    omega
  have hm : z < N / 2 := by
    have h1 : (2 * (z + 1)) / 2 ≤ N / 2 := Nat.div_le_div_right hN_ge
    rw [Nat.mul_div_right (z + 1) (by norm_num : 0 < 2)] at h1
    omega
  exact circulant_mixed_graph_valid_and_regular_general N (N / 2) z hz hm hNm
