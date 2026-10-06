import AFTD.Prelude
import AFTD.Kb.Tcs.IsParityRepr
import AFTD.Kb.Tcs.LineSyndrome

/-!
# line_cubic_parity_repr_eval_zero

Topic: quantum   Node: 2841265f4740

Provenance: helper lemma. step towards line_cubic_t_count_lower_bound

For n ≥ 5, any affine evaluation (∑_{j ∈ y} c_j = b) on all parities y ∈ S of a parity representation S of line_syndrome n forces c = 0.
-/

open Finset

theorem line_cubic_parity_repr_eval_zero_card_le_two (n : ℕ) (S : Finset (Finset (Fin n)))
    (hS : is_parity_repr S (line_syndrome n))
    (A : Finset (Fin n)) (hA1 : 1 ≤ A.card) (hA2 : A.card ≤ 2) :
    ((S.filter (fun y => A ⊆ y)).card : ZMod 2) = 0 := by
  have hrepr := hS.2 A ⟨hA1, by omega⟩
  rw [hrepr]
  unfold line_syndrome
  split_ifs with h
  · rcases h with ⟨i, hi⟩
    have hc : ({⟨i.1, by omega⟩, ⟨i.1 + 1, by omega⟩, ⟨i.1 + 2, by omega⟩} : Finset (Fin n)).card = 3 := by
      have h01 : (⟨i.1, by omega⟩ : Fin n) ≠ ⟨i.1 + 1, by omega⟩ := by
        intro heq; injection heq with heq; omega
      have h02 : (⟨i.1, by omega⟩ : Fin n) ≠ ⟨i.1 + 2, by omega⟩ := by
        intro heq; injection heq with heq; omega
      have h12 : (⟨i.1 + 1, by omega⟩ : Fin n) ≠ ⟨i.1 + 2, by omega⟩ := by
        intro heq; injection heq with heq; omega
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro hm; simp only [Finset.mem_singleton] at hm; exact h12 hm
      · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (hm | hm)
        · exact h01 hm
        · exact h02 hm
    rw [hi] at hA2
    omega
  · rfl

def line_cubic_parity_repr_eval_zero_line_triple (n : ℕ) (i : Fin (n - 2)) : Finset (Fin n) :=
  {⟨i.1, by omega⟩, ⟨i.1 + 1, by omega⟩, ⟨i.1 + 2, by omega⟩}

theorem line_cubic_parity_repr_eval_zero_mem_line_triple (n : ℕ) (i : Fin (n - 2)) (a : Fin n) :
    a ∈ line_cubic_parity_repr_eval_zero_line_triple n i ↔ a.1 = i.1 ∨ a.1 = i.1 + 1 ∨ a.1 = i.1 + 2 := by
  unfold line_cubic_parity_repr_eval_zero_line_triple
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

theorem line_cubic_parity_repr_eval_zero_pair_sum (n : ℕ)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c : Fin n → ZMod 2) (b : ZMod 2)
    (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b)
    (p q : Fin n) (hpq : p ≠ q) :
    ∑ j : Fin n, c j * line_syndrome n (insert j {p, q}) = 0 := by
  have h_zero : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (∑ j ∈ y, c j)) = 0 := by
    have h1 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (∑ j ∈ y, c j)) =
        ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), b := by
      refine sum_congr rfl (fun y hy => ?_)
      rw [mem_filter] at hy
      exact h y hy.1
    rw [h1, sum_const, nsmul_eq_mul]
    have hcard1 : 1 ≤ ({p, q} : Finset (Fin n)).card := by
      rw [card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
      omega
    have hcard2 : ({p, q} : Finset (Fin n)).card ≤ 2 := by
      rw [card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
    have hz := line_cubic_parity_repr_eval_zero_card_le_two n S hS {p, q} hcard1 hcard2
    rw [hz, zero_mul]
  have h_swap : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (∑ j ∈ y, c j)) =
      ∑ j : Fin n, c j * line_syndrome n (insert j {p, q}) := by
    have h1 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (∑ j ∈ y, c j)) =
        ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), ∑ j : Fin n, (if j ∈ y then c j else 0) := by
      refine sum_congr rfl (fun y _ => (sum_ite_mem_eq y c).symm)
    rw [h1, sum_comm]
    refine sum_congr rfl (fun j _ => ?_)
    have h2 : (∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (if j ∈ y then c j else 0)) =
        c j * ∑ y ∈ S.filter (fun y => {p, q} ⊆ y), (if j ∈ y then (1 : ZMod 2) else 0) := by
      rw [mul_sum]
      refine sum_congr rfl (fun y _ => by split_ifs <;> ring)
    rw [h2, sum_boole]
    have h3 : (S.filter (fun y => {p, q} ⊆ y)).filter (fun y => j ∈ y) =
        S.filter (fun y => insert j {p, q} ⊆ y) := by
      ext y
      simp only [mem_filter, Finset.insert_subset_iff]
      tauto
    rw [h3]
    have hcard1 : 1 ≤ (insert j ({p, q} : Finset (Fin n))).card := by
      have : (insert j ({p, q} : Finset (Fin n))).Nonempty := ⟨j, mem_insert_self _ _⟩
      exact Nonempty.card_pos this
    have hcard2 : (insert j ({p, q} : Finset (Fin n))).card ≤ 3 := by
      have h_sub := card_insert_le j ({p, q} : Finset (Fin n))
      have h_pq : ({p, q} : Finset (Fin n)).card = 2 := by
        rw [card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
      omega
    have h_repr := hS.2 (insert j {p, q}) ⟨hcard1, hcard2⟩
    rw [h_repr]
  rw [← h_swap]
  exact h_zero

theorem line_cubic_parity_repr_eval_zero_two_points (n : ℕ) (c : Fin n → ZMod 2) (a b : Fin n) (hab : a ≠ b) :
    (∑ j : Fin n, c j * (if j = a ∨ j = b then 1 else 0)) = c a + c b := by
  have h : ∀ j : Fin n, c j * (if j = a ∨ j = b then (1 : ZMod 2) else 0) =
      (if j = a then c a else 0) + (if j = b then c b else 0) := by
    intro j
    by_cases hja : j = a
    · rw [if_pos (Or.inl hja), if_pos hja]
      have hjb : j ≠ b := by rw [hja]; exact hab
      rw [if_neg hjb, hja]
      ring
    · by_cases hjb : j = b
      · rw [if_pos (Or.inr hjb), if_neg hja, if_pos hjb, hjb]
        ring
      · have hnab : ¬ (j = a ∨ j = b) := by tauto
        rw [if_neg hnab, if_neg hja, if_neg hjb]
        ring
  simp_rw [h, sum_add_distrib, sum_ite_eq']
  simp

theorem line_cubic_parity_repr_eval_zero_mid (n : ℕ)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c : Fin n → ZMod 2) (b : ZMod 2)
    (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b)
    (i : Fin (n - 2)) :
    c ⟨i.1 + 1, by omega⟩ = 0 := by
  let p : Fin n := ⟨i.1, by omega⟩
  let q : Fin n := ⟨i.1 + 2, by omega⟩
  have hpq : p ≠ q := by
    intro heq
    have : p.1 = q.1 := congrArg Fin.val heq
    change i.1 = i.1 + 2 at this
    omega
  have h_syn : ∀ j : Fin n, line_syndrome n (insert j {p, q}) =
      if j = ⟨i.1 + 1, by omega⟩ then 1 else 0 := by
    intro j
    unfold line_syndrome
    by_cases hj : j = ⟨i.1 + 1, by omega⟩
    · rw [if_pos hj]
      have hex : ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
        refine ⟨i, ?_⟩
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
        dsimp [p, q]
        subst hj
        change x.1 = i.1 + 1 ∨ x.1 = i.1 ∨ x.1 = i.1 + 2 ↔ x.1 = i.1 ∨ x.1 = i.1 + 1 ∨ x.1 = i.1 + 2
        tauto
      exact if_pos hex
    · rw [if_neg hj]
      have h_not : ¬ ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
        rintro ⟨k, hk⟩
        have hp_in : p ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        have hq_in : q ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        rw [line_cubic_parity_repr_eval_zero_mem_line_triple] at hp_in hq_in
        dsimp [p, q] at hp_in hq_in
        have hki : k.1 = i.1 := by omega
        have h_mid : (⟨i.1 + 1, by omega⟩ : Fin n) ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
          dsimp
          omega
        change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
        rw [← hk] at h_mid
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h_mid
        dsimp [p, q] at h_mid
        change i.1 + 1 = j.1 ∨ i.1 + 1 = i.1 ∨ i.1 + 1 = i.1 + 2 at h_mid
        have : j = ⟨i.1 + 1, by omega⟩ := by
          ext
          change j.1 = i.1 + 1
          omega
        exact hj this
      exact if_neg h_not
  have h_pair := line_cubic_parity_repr_eval_zero_pair_sum n S hS c b h p q hpq
  have h_eval : (∑ j : Fin n, c j * line_syndrome n (insert j {p, q})) = c ⟨i.1 + 1, by omega⟩ := by
    have h_term : ∀ j : Fin n, c j * line_syndrome n (insert j {p, q}) =
        if j = ⟨i.1 + 1, by omega⟩ then c ⟨i.1 + 1, by omega⟩ else 0 := by
      intro j
      rw [h_syn]
      split_ifs with hj
      · subst hj; ring
      · ring
    simp_rw [h_term]
    rw [sum_ite_eq']
    simp
  rw [h_eval] at h_pair
  exact h_pair

theorem line_cubic_parity_repr_eval_zero_zero (n : ℕ) (hn : 5 ≤ n)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c : Fin n → ZMod 2) (b : ZMod 2)
    (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b) :
    c ⟨0, by omega⟩ = 0 := by
  let p : Fin n := ⟨1, by omega⟩
  let q : Fin n := ⟨2, by omega⟩
  have hpq : p ≠ q := by
    intro heq
    have : p.1 = q.1 := congrArg Fin.val heq
    change 1 = 2 at this
    omega
  have h_pair := line_cubic_parity_repr_eval_zero_pair_sum n S hS c b h p q hpq
  have h_syn : ∀ j : Fin n, line_syndrome n (insert j {p, q}) =
      if j = ⟨0, by omega⟩ ∨ j = ⟨3, by omega⟩ then 1 else 0 := by
    intro j
    unfold line_syndrome
    by_cases hj : j = ⟨0, by omega⟩ ∨ j = ⟨3, by omega⟩
    · rw [if_pos hj]
      rcases hj with hj0 | hj3
      · have hex : ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
          refine ⟨⟨0, by omega⟩, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
          dsimp [p, q]
          subst hj0
          change x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 ↔ x.1 = 0 ∨ x.1 = 0 + 1 ∨ x.1 = 0 + 2
          tauto
        exact if_pos hex
      · have hex : ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
          refine ⟨⟨1, by omega⟩, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
          dsimp [p, q]
          subst hj3
          change x.1 = 3 ∨ x.1 = 1 ∨ x.1 = 2 ↔ x.1 = 1 ∨ x.1 = 1 + 1 ∨ x.1 = 1 + 2
          tauto
        exact if_pos hex
    · rw [if_neg hj]
      have h_not : ¬ ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
        rintro ⟨k, hk⟩
        have hp_in : p ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        have hq_in : q ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        rw [line_cubic_parity_repr_eval_zero_mem_line_triple] at hp_in hq_in
        dsimp [p, q] at hp_in hq_in
        change 1 = k.1 ∨ 1 = k.1 + 1 ∨ 1 = k.1 + 2 at hp_in
        change 2 = k.1 ∨ 2 = k.1 + 1 ∨ 2 = k.1 + 2 at hq_in
        have hk_cases : k.1 = 0 ∨ k.1 = 1 := by omega
        rcases hk_cases with hk0 | hk1
        · have hj0 : j = ⟨0, by omega⟩ := by
            have h0 : (⟨0, by omega⟩ : Fin n) ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
              rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
              dsimp
              omega
            change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
            rw [← hk] at h0
            simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h0
            dsimp [p, q] at h0
            ext; change j.1 = 0; omega
          exact hj (Or.inl hj0)
        · have hj3 : j = ⟨3, by omega⟩ := by
            have h3 : (⟨3, by omega⟩ : Fin n) ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
              rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
              dsimp
              omega
            change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
            rw [← hk] at h3
            simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h3
            dsimp [p, q] at h3
            ext; change j.1 = 3; omega
          exact hj (Or.inr hj3)
      exact if_neg h_not
  simp_rw [h_syn] at h_pair
  have h_eval := line_cubic_parity_repr_eval_zero_two_points n c ⟨0, by omega⟩ ⟨3, by omega⟩ (by
    intro heq
    have : (⟨0, by omega⟩ : Fin n).1 = (⟨3, by omega⟩ : Fin n).1 := congrArg Fin.val heq
    change 0 = 3 at this
    omega)
  rw [h_eval] at h_pair
  have h3 : c ⟨3, by omega⟩ = 0 := by
    have := line_cubic_parity_repr_eval_zero_mid n S hS c b h ⟨2, by omega⟩
    exact this
  rw [h3, add_zero] at h_pair
  exact h_pair

theorem line_cubic_parity_repr_eval_zero_last (n : ℕ) (hn : 5 ≤ n)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c : Fin n → ZMod 2) (b : ZMod 2)
    (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b) :
    c ⟨n - 1, by omega⟩ = 0 := by
  let p : Fin n := ⟨n - 3, by omega⟩
  let q : Fin n := ⟨n - 2, by omega⟩
  have hpq : p ≠ q := by
    intro heq
    have : p.1 = q.1 := congrArg Fin.val heq
    change n - 3 = n - 2 at this
    omega
  have h_pair := line_cubic_parity_repr_eval_zero_pair_sum n S hS c b h p q hpq
  have h_syn : ∀ j : Fin n, line_syndrome n (insert j {p, q}) =
      if j = ⟨n - 4, by omega⟩ ∨ j = ⟨n - 1, by omega⟩ then 1 else 0 := by
    intro j
    unfold line_syndrome
    by_cases hj : j = ⟨n - 4, by omega⟩ ∨ j = ⟨n - 1, by omega⟩
    · rw [if_pos hj]
      rcases hj with hj4 | hj1
      · have hex : ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
          refine ⟨⟨n - 4, by omega⟩, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
          dsimp [p, q]
          subst hj4
          change x.1 = n - 4 ∨ x.1 = n - 3 ∨ x.1 = n - 2 ↔ x.1 = n - 4 ∨ x.1 = (n - 4) + 1 ∨ x.1 = (n - 4) + 2
          have h1 : (n - 4) + 1 = n - 3 := by omega
          have h2 : (n - 4) + 2 = n - 2 := by omega
          rw [h1, h2]
        exact if_pos hex
      · have hex : ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
          refine ⟨⟨n - 3, by omega⟩, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
          dsimp [p, q]
          subst hj1
          change x.1 = n - 1 ∨ x.1 = n - 3 ∨ x.1 = n - 2 ↔ x.1 = n - 3 ∨ x.1 = (n - 3) + 1 ∨ x.1 = (n - 3) + 2
          have h1 : (n - 3) + 1 = n - 2 := by omega
          have h2 : (n - 3) + 2 = n - 1 := by omega
          rw [h1, h2]
          tauto
        exact if_pos hex
    · rw [if_neg hj]
      have h_not : ¬ ∃ k : Fin (n - 2), insert j {p, q} = line_cubic_parity_repr_eval_zero_line_triple n k := by
        rintro ⟨k, hk⟩
        have hp_in : p ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        have hq_in : q ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
          change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
          rw [← hk]
          simp
        rw [line_cubic_parity_repr_eval_zero_mem_line_triple] at hp_in hq_in
        dsimp [p, q] at hp_in hq_in
        change n - 3 = k.1 ∨ n - 3 = k.1 + 1 ∨ n - 3 = k.1 + 2 at hp_in
        change n - 2 = k.1 ∨ n - 2 = k.1 + 1 ∨ n - 2 = k.1 + 2 at hq_in
        have hk_cases : k.1 = n - 4 ∨ k.1 = n - 3 := by
          have : k.1 < n - 2 := k.isLt
          omega
        rcases hk_cases with hk4 | hk3
        · have hj4 : j = ⟨n - 4, by omega⟩ := by
            have h0 : (⟨n - 4, by omega⟩ : Fin n) ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
              rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
              dsimp
              omega
            change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
            rw [← hk] at h0
            simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h0
            dsimp [p, q] at h0
            ext; change j.1 = n - 4; omega
          exact hj (Or.inl hj4)
        · have hj1 : j = ⟨n - 1, by omega⟩ := by
            have h0 : (⟨n - 1, by omega⟩ : Fin n) ∈ line_cubic_parity_repr_eval_zero_line_triple n k := by
              rw [line_cubic_parity_repr_eval_zero_mem_line_triple]
              dsimp
              omega
            change {j, p, q} = line_cubic_parity_repr_eval_zero_line_triple n k at hk
            rw [← hk] at h0
            simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at h0
            dsimp [p, q] at h0
            ext; change j.1 = n - 1; omega
          exact hj (Or.inr hj1)
      exact if_neg h_not
  simp_rw [h_syn] at h_pair
  have h_eval := line_cubic_parity_repr_eval_zero_two_points n c ⟨n - 4, by omega⟩ ⟨n - 1, by omega⟩ (by
    intro heq
    have : (⟨n - 4, by omega⟩ : Fin n).1 = (⟨n - 1, by omega⟩ : Fin n).1 := congrArg Fin.val heq
    change n - 4 = n - 1 at this
    omega)
  rw [h_eval] at h_pair
  have h4 : c ⟨n - 4, by omega⟩ = 0 := by
    have := line_cubic_parity_repr_eval_zero_mid n S hS c b h ⟨n - 5, by omega⟩
    have heq : (⟨(⟨n - 5, by omega⟩ : Fin (n - 2)).1 + 1, by omega⟩ : Fin n) = ⟨n - 4, by omega⟩ := by
      ext; change (n - 5) + 1 = n - 4; omega
    rw [← heq]
    exact this
  rw [h4, zero_add] at h_pair
  exact h_pair

/-- Any affine evaluation on all parities of a parity representation of the line cubic syndrome forces c = 0. -/
theorem line_cubic_parity_repr_eval_zero (n : ℕ) (hn : 5 ≤ n)
    (S : Finset (Finset (Fin n))) (hS : is_parity_repr S (line_syndrome n))
    (c : Fin n → ZMod 2) (b : ZMod 2)
    (h : ∀ y ∈ S, (∑ j ∈ y, c j) = b) :
    c = 0 := by
  ext x
  have hx : x.1 = 0 ∨ x.1 = n - 1 ∨ (1 ≤ x.1 ∧ x.1 ≤ n - 2) := by
    have : x.1 < n := x.isLt
    omega
  rcases hx with h0 | hn1 | hmid
  · have heq : x = ⟨0, by omega⟩ := by ext; exact h0
    rw [heq]
    exact line_cubic_parity_repr_eval_zero_zero n hn S hS c b h
  · have heq : x = ⟨n - 1, by omega⟩ := by ext; exact hn1
    rw [heq]
    exact line_cubic_parity_repr_eval_zero_last n hn S hS c b h
  · have heq : x = ⟨(⟨x.1 - 1, by omega⟩ : Fin (n - 2)).1 + 1, by omega⟩ := by
      ext; change x.1 = (x.1 - 1) + 1; omega
    rw [heq]
    exact line_cubic_parity_repr_eval_zero_mid n S hS c b h ⟨x.1 - 1, by omega⟩
