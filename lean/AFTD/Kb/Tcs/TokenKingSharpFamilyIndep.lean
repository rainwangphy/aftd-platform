import AFTD.Prelude
import AFTD.Kb.Tcs.TokenKingSharpFamily
import AFTD.Kb.Tcs.CyclicDist
import AFTD.Kb.Tcs.TokenGraph

/-!
# token_king_sharp_family_indep

Topic: graphs   Node: 5019f7f8ff20

Provenance: helper lemma. arXiv:2611.22830

For every natural number n divisible by 4 with 8 ≤ n, the candidate sharp family token_king_sharp_family n is an independent set in the two-token graph token_graph (SimpleGraph.cycleGraph n) 2.
-/

private lemma token_king_sharp_family_indep_cyclic_dist_comm (n : ℕ) [NeZero n] (u v : Fin n) :
    cyclic_dist n u v = cyclic_dist n v u := by
  unfold cyclic_dist
  by_cases huv : u = v
  · subst huv; simp
  · have hv : v - u ≠ 0 := fun h0 => huv (sub_eq_zero.mp h0).symm
    have h1 : u - v = -(v - u) := by abel
    have h2 : (u - v).val = n - (v - u).val := by
      rw [h1, Fin.val_neg, if_neg hv]
    have h3 : (v - u).val < n := (v - u).isLt
    rw [h2]
    have h4 : n - (n - (v - u).val) = (v - u).val := by omega
    rw [h4]
    exact Nat.min_comm _ _

private lemma token_king_sharp_family_indep_two_adj_decomp {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hA : A.card = 2) (hB : B.card = 2)
    (h : (token_graph G 2).Adj ⟨A, hA⟩ ⟨B, hB⟩) :
    ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ A = {x, y} ∧ B = {x, z} ∧ G.Adj y z := by
  simp only [token_graph] at h
  obtain ⟨u, v, huv, hdiff⟩ := h
  have huvne : u ≠ v := G.ne_of_adj huv
  have hcardUV : ({u, v} : Finset V).card = 2 := Finset.card_pair huvne
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hdiff' : A \ B ∪ B \ A = {u, v} := by
    rw [← Finset.symmDiff_def]
    exact hdiff
  have hc : (A \ B).card + (B \ A).card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, hdiff', hcardUV]
  have hk2 : (A ∩ B).card ≤ 2 := by
    rw [← hA]; exact Finset.card_le_card Finset.inter_subset_left
  have hca : (A \ B).card = 2 - (A ∩ B).card := by
    rw [Finset.card_sdiff, hA, Finset.inter_comm]
  have hcb : (B \ A).card = 2 - (A ∩ B).card := by
    rw [Finset.card_sdiff, hB]
  have hk : (A ∩ B).card = 1 := by omega
  have hcay : (A \ B).card = 1 := by omega
  have hcbz : (B \ A).card = 1 := by omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcay
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcbz
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hk
  have hyAB : y ∈ A \ B := by rw [hy]; exact Finset.mem_singleton_self y
  have hzBA : z ∈ B \ A := by rw [hz]; exact Finset.mem_singleton_self z
  have hyB : y ∉ B := (Finset.mem_sdiff.mp hyAB).2
  have hzB : z ∈ B := (Finset.mem_sdiff.mp hzBA).1
  have hzA : z ∉ A := (Finset.mem_sdiff.mp hzBA).2
  have hxA : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
  have hxA' : x ∈ A := (Finset.mem_inter.mp hxA).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hxA).2
  have hxy : x ≠ y := fun hh => hyB (hh ▸ hxB)
  have hxz : x ≠ z := fun hh => hzA (hh ▸ hxA')
  have hyz : y ≠ z := fun hh => hyB (hh ▸ hzB)
  have hAxy : A = {x, y} := by
    rw [← Finset.sdiff_union_inter A B, hy, hx]
    ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hBxz : B = {x, z} := by
    have h := Finset.sdiff_union_inter B A
    rw [Finset.inter_comm] at h
    rw [← h, hz, hx]
    ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hpair : ({y, z} : Finset V) = {u, v} := by
    rw [← hdiff', hy, hz]
    ext w; simp [Finset.mem_insert, Finset.mem_singleton]
  have hyuv : y = u ∨ y = v := by
    have : y ∈ ({u, v} : Finset V) := by rw [← hpair]; simp
    simpa using this
  have hzuv : z = u ∨ z = v := by
    have : z ∈ ({u, v} : Finset V) := by rw [← hpair]; simp
    simpa using this
  refine ⟨x, y, z, hxy, hxz, hyz, hAxy, hBxz, ?_⟩
  rcases hyuv with rfl | rfl
  · rcases hzuv with rfl | rfl
    · exact absurd rfl hyz
    · exact huv
  · rcases hzuv with rfl | rfl
    · exact huv.symm
    · exact absurd rfl hyz

private lemma token_king_sharp_family_indep_arith (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (p q : ℕ) (hp : p < n) (hq : q < n) (hqp : q = (p + 1) % n)
    (ha : min p (n - p) = n / 2 ∨ (min p (n - p) ≤ n / 2 - 3 ∧ min p (n - p) % 2 = 1))
    (hb : min q (n - q) = n / 2 ∨ (min q (n - q) ≤ n / 2 - 3 ∧ min q (n - q) % 2 = 1)) : False := by
  obtain ⟨k, hk⟩ := h4
  have hn2 : n = 2 * (n / 2) := by omega
  have hqdec : q = p + 1 ∨ (p = n - 1 ∧ q = 0) := by
    have hp1 : p + 1 ≤ n := by omega
    rcases Nat.lt_or_eq_of_le hp1 with h | h
    · left; rw [hqp, Nat.mod_eq_of_lt h]
    · right
      refine ⟨by omega, ?_⟩
      rw [hqp, ← h, Nat.mod_self]
  rcases hqdec with hq1 | ⟨hpfirst, hq0⟩
  · subst hq1
    rcases ha with ha1 | ⟨ha_le, ha_odd⟩
    · have hp_eq : p = n / 2 := by
        by_cases hh : p ≤ n - p
        · rw [min_eq_left hh] at ha1; exact ha1
        · rw [min_eq_right (le_of_lt (Nat.lt_of_not_le hh))] at ha1; omega
      have hbval : min (p + 1) (n - (p + 1)) = n / 2 - 1 := by
        have h1 : n - (p + 1) ≤ p + 1 := by omega
        rw [min_eq_right h1]; omega
      rw [hbval] at hb
      rcases hb with h | ⟨h, _⟩ <;> omega
    · have hp_cases : p = min p (n - p) ∨ p = n - min p (n - p) := by
        by_cases hh : p ≤ n - p
        · left; rw [min_eq_left hh]
        · right
          have hmin : min p (n - p) = n - p := min_eq_right (le_of_lt (Nat.lt_of_not_le hh))
          omega
      rcases hp_cases with hpA | hpB
      · have hpodd : p % 2 = 1 := by rw [hpA]; exact ha_odd
        have hple : p ≤ n / 2 - 3 := by rw [hpA]; exact ha_le
        have hbval : min (p + 1) (n - (p + 1)) = p + 1 := by
          rw [min_eq_left]; omega
        rw [hbval] at hb
        have hmod : (p + 1) % 2 = 0 := by omega
        rcases hb with h | ⟨h, hodd⟩ <;> omega
      · have hpodd : (min p (n - p)) % 2 = 1 := ha_odd
        have hbval : min (p + 1) (n - (p + 1)) = min p (n - p) - 1 := by
          have h1 : n - (p + 1) ≤ p + 1 := by omega
          rw [min_eq_right h1]; omega
        rw [hbval] at hb
        have hmod : (min p (n - p) - 1) % 2 = 0 := by omega
        rcases hb with h | ⟨h, hodd⟩ <;> omega
  · have hb0 : min q (n - q) = 0 := by rw [hq0]; simp
    rw [hb0] at hb
    rcases hb with h | ⟨h, hodd⟩ <;> omega

private lemma token_king_sharp_family_indep_cond_of_mem {n : ℕ}
    (e : { s : Finset (Fin n) // s.card = 2 })
    (he : e ∈ token_king_sharp_family n) (x y : Fin n) (h : e.val = {x, y}) :
    cyclic_dist n x y = n / 2 ∨
      (cyclic_dist n x y ≤ n / 2 - 3 ∧ cyclic_dist n x y % 2 = 1) := by
  haveI : NeZero n := ⟨by have := x.isLt; omega⟩
  simp only [token_king_sharp_family, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨u, v, huv, hcond⟩ := he
  have hc : ({u, v} : Finset (Fin n)).card = 2 := by rw [← huv]; exact e.property
  have hune : u ≠ v := by
    intro hh
    rw [hh] at hc
    simp at hc
  have huv_eq : ({u, v} : Finset (Fin n)) = {x, y} := by rw [← huv, h]
  have hu : u = x ∨ u = y := by
    have : u ∈ ({x, y} : Finset (Fin n)) := by rw [← huv_eq]; simp
    simpa using this
  have hv : v = x ∨ v = y := by
    have : v ∈ ({x, y} : Finset (Fin n)) := by rw [← huv_eq]; simp
    simpa using this
  rcases hu with hux | huy
  · rcases hv with hvx | hvy
    · exact absurd (hux.trans hvx.symm) hune
    · rw [hux, hvy] at hcond; exact hcond
  · rcases hv with hvx | hvy
    · rw [huy, hvx] at hcond
      rw [token_king_sharp_family_indep_cyclic_dist_comm n y x] at hcond
      exact hcond
    · exact absurd (huy.trans hvy.symm) hune

private lemma token_king_sharp_family_indep_key_fin (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n)
    (x y z : Fin n)
    (hy : cyclic_dist n x y = n / 2 ∨
      (cyclic_dist n x y ≤ n / 2 - 3 ∧ cyclic_dist n x y % 2 = 1))
    (hz : cyclic_dist n x z = n / 2 ∨
      (cyclic_dist n x z ≤ n / 2 - 3 ∧ cyclic_dist n x z % 2 = 1))
    (hyz : (y - z).val = 1) : False := by
  haveI : NeZero n := ⟨by have := x.isLt; omega⟩
  have hq : (x - z).val = ((x - y).val + 1) % n := by
    have h1 : x - z = (x - y) + (y - z) := by abel
    rw [h1, Fin.val_add, hyz]
  exact token_king_sharp_family_indep_arith n hn h4 (x - y).val (x - z).val
    (x - y).isLt (x - z).isLt hq (by simpa [cyclic_dist] using hy) (by simpa [cyclic_dist] using hz)

/-- When 4 divides n >= 8, the candidate sharpness family is independent in the two-token cycle graph. -/
theorem token_king_sharp_family_indep (n : ℕ) (h4 : 4 ∣ n) (hn : 8 ≤ n) :
    (token_graph (SimpleGraph.cycleGraph n) 2).IsIndepSet
      ((token_king_sharp_family n) : Set { s : Finset (Fin n) // s.card = 2 }) := by
  rw [SimpleGraph.IsIndepSet]
  intro e he e' he' hne hcon
  obtain ⟨x, y, z, hxy, hxz, hyz, hA, hB, hyzadj⟩ :=
    token_king_sharp_family_indep_two_adj_decomp (SimpleGraph.cycleGraph n) e.val e'.val
      e.property e'.property hcon
  have he1 : e ∈ token_king_sharp_family n := by simpa using he
  have he2 : e' ∈ token_king_sharp_family n := by simpa using he'
  have hycond := token_king_sharp_family_indep_cond_of_mem e he1 x y hA
  have hzcond := token_king_sharp_family_indep_cond_of_mem e' he2 x z hB
  rcases SimpleGraph.cycleGraph_adj'.mp hyzadj with h | h
  · exact token_king_sharp_family_indep_key_fin n hn h4 x y z hycond hzcond h
  · exact token_king_sharp_family_indep_key_fin n hn h4 x z y hzcond hycond h
